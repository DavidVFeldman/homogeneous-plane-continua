# Commission: batch 113 — the cube cycle in `ℤ^d`, the density lemma in every dimension, and Bing's Theorem 2 as stated

**Go!** Runs on top of the batch-112 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch113.md` — this text (also pasted into the prompt);
* `CubeCycle.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/CubeCycle.lean` and add `import HPC.Plane.CubeCycle` at the end of the root
  `HPC.lean`. Existing files to be edited: `Axioms.lean`/`axioms.txt`; and, for the last item
  only, `HPC/Plane/LatticeCycle.lean` (the open statement and its three consequences move or get
  their proof — see the docstring of `geomLemma'_of_two_le_rank'`), `OPEN.md` (item 4 closed:
  remove it, renumber nothing — leave the numbers of the remaining items as they are and say
  "item 4: closed in batch 113"), `README.md` (one line). Shapes may be adjusted with the change
  recorded; split the file if it passes 1000 lines.

The report names the commission read in its first line.

## 0. On batch 112

Audited: all five items proved, no refutation; 296 declarations, `sorryAx` in 10. The
`ℓ¹`-case estimate with `‖w‖ = √r`, `r ≤ L`, and the dropped unused hypotheses
(`h1`, `h2` of `diagDir_not_mem_span`; `[CompleteSpace E]` on the pullback) are accepted. The
stray `theorems-3-4-scheduling(18).md` at the root may be removed in this batch; the copy uploaded
with this commission replaces `doc/theorems-3-4-scheduling.md`.

## 1. Items

1. **Cube loops** (`eZ`, `InCube`, `InCubeInt`, `CubeConnected`, `faceDir`, `CubeLoop`,
   `exists_cubeLoop_two`, `exists_cubeLoop_succ`, `exists_cubeLoop`). The structure's fields are
   exactly what the splice uses; if the splice needs one more (say, that a designated point is
   not a point of any *other* designated edge's interior — there is none, edges have no interior
   points — or that the loop's points other than the designated ones avoid something), add it,
   prove it in the base and the step, and record it. `exists_cubeLoop_two` transports
   `LatticeCycleAux.loop0`, `pA 0`, `pB 0` along `ℤ × ℤ ≃ (Fin 2 → ℤ)` (`![p.1, p.2]`); every
   field is a finite check (`decide`, as `L_step`, `L_inj`, `L_mem`, `L_pair` there), except
   `big`: `18 ≤ 24`. `exists_cubeLoop_succ`: the header's doubling. Choose the edge `p → q` of
   `l` that is not a designated edge, and the edge `p' → q'` with `p'`, `q'` not designated points
   (counting: `≤ 4d` designated points touch `≤ 8d` of the `L ≥ 8d + 2` edges). The new loop
   as a function `ℕ → (Fin (d+1) → ℤ)` by cases on the index (bottom block of length `L`, column
   of length `5`, top block of length `L`, column of length `5`); `Fin.snoc` for the extension
   by one coordinate. Prove the fields; `big` by arithmetic.

2. **The cycle** (`exists_latticeCycleN`, `exists_latticePathN_of_cubes`). The plane proof
   (`LCyc.Inv`, `inv_rot`, `inv_splice`, `inv_grow`, `exists_inv_sub`), generalised: replace
   `Fin 4` sides by faces `(i, b)`, `dvec` by `faceDir`, `pA s i`/`pB s i` by
   `tr s (l.A i b)`/`tr s (l.B i b)` with `tr s p = 8 • s + p`, the `decide` facts `D_*`, `L_*`,
   `side_eq`, `pair_eq`, `not_inSqInt_side` by consequences of the `CubeLoop` fields and of
   `InCubeInt`. The detour across face `(i, b)` of `s` into `ℓ = s + faceDir i b`: with
   `e = faceDir i b`, `x → y` the designated edge of `(i, b)` in `s` (either orientation),
   `x + e, x + 2 e = tr ℓ (l.A i (¬b))` (by `A_opp`/`B_opp` — check the direction of the
   translation for both values of `b`), then `ℓ`'s loop the long way to `y + 2 e`, then `y + e`.
   Invariant length `L₀ + (L₀ + 2)(N - 1)` (`L₀ = l.L`). The path: drop the closing step;
   `n ≥ 23`.

3. **Cubes of `E`** (`cubeSet`, `cubesMeeting`, `exists_orthonormal_basis_fin`,
   `cubesMeeting_finite`, `exists_cube_mem`, `diam_cubeSet_le`, `latticePtN_mem_cubeSet`,
   `cubesMeeting_connected`): the plane's `sqSet` lemmas with `Fin d`; the connectedness proof
   by induction on the number of coordinates in which the two cubes differ.

4. **Assembly** (`geomLemma'_of_finrank_ge_three`, `geomLemma'_of_finrank`,
   `geomLemma'_of_two_le_rank'`). The last is `geomLemma'_of_subspaces` applied with
   `geomLemma'_of_finrank` on each subspace `F` (`F` is a finite-dimensional inner product space
   with `2 ≤ finrank`). Then close the open target: `geomLemma'_of_two_le_rank` in
   `LatticeCycle.lean` cannot see this file. Preferred: **move** `geomLemma'_of_two_le_rank`,
   `dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951` from `LatticeCycle.lean` to the end of
   `CubeCycle.lean`, with `geomLemma'_of_two_le_rank` proved (and `geomLemma'_of_two_le_rank'`
   then not needed — drop the primed name), their docstrings updated ("Bing 1951 (Pacific),
   Theorem 2" / "Bing 1951 (Duke), Theorem 2", no longer conditional), the `-- OPEN` marker
   removed; `Axioms.lean`: these four move from *Open targets* / *Consequences* to the Pacific and
   Duke groups; `OPEN.md` item 4 closed as above; `README.md`: Theorem 2 of both papers now
   "in Euclidean space of dimension `≥ 2` and in Hilbert space" (every complete real inner
   product space of dimension `≥ 2`). Expected `sorryAx`: exactly **6** lines (`theorem3_end`,
   `covering_step`, `theorem14`, `fugate_cor1`, `theorem15`, `exists_description_covering`).

Report each item *proved / refuted / open with the obstruction stated*; refutations first. If
item 1 or 2 is not finished, leave the `sorry` where it is, do **not** move the open target, and
report the obstruction; items 3–4 may then still be proved from the `sorry`.

## 2. Deliverables

1. Items 1–4; `#print axioms` in `axioms-batch113.txt`; `axioms.txt` regenerated.
2. Report: first line names the commission read; items in order; the exact loop length and cycle
   length formulas; the list of `CubeLoop` fields added, if any; which files were edited.
3. Not attempted: the four remaining open targets.

## 3. Next

Duke Theorems 6–7 on a polygonal-Jordan-curve-theorem interface (to be designed), or the
remaining open targets.
