Commission read: `COMMISSION-batch113.md` — batch 113, the cube cycle in `ℤ^d`, the density lemma in every dimension, and Bing's Theorem 2 as stated.

# Report, batch 113

**Refutations:** none. No statement of the skeleton is false.

All four items are **proved**. None is open. The three new files contain no `sorry`. The 13
skeleton theorems of items 1–4 and the four moved statements (`geomLemma'_of_two_le_rank`,
`dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951`) depend only on
`[propext, Classical.choice, Quot.sound]` (`doc/batches/audits/axioms-batch113.txt`, from
`doc/batches/audits/Axioms113.lean`). OPEN.md item 4 is closed. The four remaining open targets
were not attempted, as §2.3 specifies.

## 0. Files

* `HPC/Plane/CubeLoop.lean` (new). The definitions of the skeleton (`eZ`, `InCube`, `InCubeInt`,
  `CubeConnected`, `faceDir`, `CubeLoop`, unchanged) and item 1. Helpers in namespace
  `HPC.Plane.CubeLoopAux`: unit steps along `faceDir`, the loop opened at an edge (`fwd`,
  `fwd_edge`), the loop opened at a designated edge in either direction (`IsOpenedLoop`,
  `exists_isOpenedLoop`), extension by a last coordinate (`ext = Fin.snoc`), the counting lemma
  `exists_two_free_edges`, the doubled loop `dblPt`/`dblA`/`dblB`, the transport `toV`.
* `HPC/Plane/CubeCycleAux.lean` (new). Item 2's invariant and splice, namespace `HPC.Plane.CCyc`
  (`tr`, `side_eq`, `pair_eq`, `Good`, `Inv`, `inv_rot`, `inv_splice`, `inv_base`, `inv_grow`,
  `exists_inv_sub`, `exists_inv`), and `exists_latticeCycleN_of_loop` (the cycle with its exact
  length).
* `HPC/Plane/CubeCycle.lean` (from the skeleton). Item 2 (`exists_latticeCycleN`,
  `exists_latticePathN_of_cubes`), item 3, item 4, and the four statements moved from
  `LatticeCycle.lean`.
* The split (the commission allows it) keeps every file under 1000 lines; the definitions had to
  move to the first file because items 1 and 2 use them.

Existing files edited: `HPC.lean` (`import HPC.Plane.CubeCycle` at the end);
`HPC/Plane/LatticeCycle.lean` (the four general-`E` statements removed, a note left in their place,
module doc updated); `Axioms.lean` / `axioms.txt`; `OPEN.md` (item 4: "closed in batch 113", other
numbers unchanged); `README.md` (Theorem 2 of the Duke and Pacific papers: "in Euclidean space of
dimension `≥ 2` and in Hilbert space"; the batch count there was left as it was);
`doc/theorems-3-4-scheduling.md` (replaced by the copy uploaded with this commission). The root
files `theorems-3-4-scheduling(18).md` and `(19).md` were removed; the commission is filed as
`doc/batches/COMMISSION-batch113.md` and the skeleton as `doc/batches/skeletons/CubeCycle.lean`.
Not edited (they still mention the former open status in prose): the module docs of
`HPC/Plane/BandN.lean` and `HPC/Plane/Most51.lean`, and `HPC/Archive/Most51Geom.lean`.

## 1. Cube loops — proved

* `exists_cubeLoop_two`: `cubeLoopTwo` is `LCyc.Lfun` transported along `p ↦ ![p.1, p.2]`, with
  `A i b = toV (pA 0 j)`, `B i b = toV (pB 0 j)`, `j = 0, 1, 2, 3` for the faces
  `(0, true), (1, true), (0, false), (1, false)`. Injectivity, steps, membership and edges from
  `L_inj`, `L_step`, `L_mem`, `L_pair`; `A_coord`, `B_coord`, `distinct`, `AB_ne`, `A_opp`,
  `B_opp` by `decide`; `big` is `18 ≤ 24`.
* `exists_cubeLoop_succ`: two edges `k₀ ≠ k₁` of `l` with no designated endpoint
  (`exists_two_free_edges`: the designated points form a set of at most `4d` points; the edges
  touching it number at most `8d`, and `L ≥ 8d + 2`). With `r j = c ((k₀ + 1 + j) mod L)` (the
  loop opened at `k₀`, from `c (k₀+1)` to `c k₀`), the new loop is
  `r 0 … r (L-1)` at height `1`, the column of `c k₀` at heights `2 … 6`, `r (L-1) … r 0` at
  height `7`, the column of `c (k₀+1)` at heights `6 … 2`. The old designated edges are inherited
  at height `1`; the new faces get the edge `c k₁ → c (k₁+1)` at heights `1` (face `(d, false)`)
  and `7` (face `(d, true)`).
* `exists_cubeLoop`: induction on `d ≥ 2` (through `exists_cubeLoop_ge`, which also records
  `24 ≤ L`, needed for the `24 ≤ L` of item 2).

**Loop length:** `L₂ = 24`, `L_{d+1} = 2 L_d + 10`, i.e. `L_d = 34 · 2^(d-2) - 10`.

**`CubeLoop` fields added:** none. The structure is used exactly as in the skeleton.

**Shape change:** `exists_cubeLoop_succ` drops the hypothesis `2 ≤ d` (unused: the field `big`
gives the two edges).

## 2. The cycle — proved

The plane proof generalised as commissioned. The detour across face `(i, b)` of `s` into
`ℓ = s + faceDir i b`, `e = faceDir i b`: the cycle is rotated so that the designated edge `x → y`
of `(i, b)` is the closing edge; then `x + e`, the loop of `ℓ` opened at its designated edge of
the face `(i, ¬b)` from `x + 2e` to `y + 2e`, and `y + e` are appended. The identity
`tr s (A i b) + 2e = tr ℓ (A i (¬b))` (and the same for `B`) holds for both values of `b`
(`A_tr_opp`, `B_tr_opp`, from `A_opp`, `B_opp`). The decide facts of the plane are replaced by:
* `side_eq` (a side point determines its face up to the cube on either side): a side point has
  exactly one coordinate `≡ 0 (mod 8)`, the face axis, since the designated points are depth-1
  points (`A_mem`/`B_mem` with `mem`);
* `pair_eq` (a designated pair determines cube and face): from `InCubeInt` uniqueness and
  `distinct`;
* the detour facts: from `IsOpenedLoop` (`exists_isOpenedLoop`), which gives the opened loop in
  either direction with every other designated edge as one of its edges.

**Cycle length:** `L₀ + (L₀ + 2)(N - 1)` for the loop length `L₀ = l.L` and `N = |T|`
(`exists_latticeCycleN_of_loop`). `exists_latticeCycleN` uses a loop with `L₀ ≥ 24`;
`exists_latticePathN_of_cubes` drops the closing step (`n = L - 1 ≥ 23`).

## 3. Cubes of `E` — proved

`exists_orthonormal_basis_fin` (`stdOrthonormalBasis` reindexed), `cubesMeeting_finite` (each
index coordinate in `[-M, M]`, `Set.Finite.pi`), `exists_cube_mem` (floors),
`diam_cubeSet_le` (`‖x - y‖² = Σ aᵢ² ≤ d δ²`), `latticePtN_mem_cubeSet` (`⟪latticePtN e δ p, e i⟫ =
δ p i`), and `cubesMeeting_connected`: as in the plane up to the point `x ∈ g` in cubes `a ∈ A`
and `b ∉ A`; then induction on the number of coordinates where a cube `a' ∈ A` containing `x`
differs from `b`: replacing one coordinate of `a'` by that of `b` gives a cube containing `x`
(so in `T`) adjacent to `a'` (the coordinates differ by `1`), hence in `A`.

## 4. Assembly — proved

* `geomLemma'_of_finrank_ge_three`: `δ = ε / (4 √d)`, so `√d δ = ε/4`; links `≤ 2δ ≤ ε/2 < ε`;
  union within `δ/8 + δ/8 + ε/4 < ε` of `g`; `g` within `ε/4 + δ/8 < ε` of the union.
* `geomLemma'_of_finrank`: `finrank = 2` (`geomLemma'_of_finrank_two`) or `≥ 3`.
* The open target is closed by the preferred option: `geomLemma'_of_two_le_rank`,
  `dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951` are **moved** from `LatticeCycle.lean` to the
  end of `CubeCycle.lean` with the same statements; `geomLemma'_of_two_le_rank` is
  `geomLemma'_of_subspaces hdim fun _ _ h2 => geomLemma'_of_finrank h2`. The primed
  `geomLemma'_of_two_le_rank'` of the skeleton is dropped. Docstrings updated ("Bing 1951
  (Pacific), Theorem 2" / "Bing 1951 (Duke), Theorem 2", no longer conditional); no `-- OPEN`
  marker remains. The instance argument `[CompleteSpace E]` of the four statements is kept as
  stated, although the proof does not use it (noted in the docstring of
  `geomLemma'_of_two_le_rank`).

## 5. Audit

* `Axioms.lean`: `theorem2_1951` moved from *Consequences* to the Duke group ("Theorem 2 (batch
  113)"); `geomLemma'_of_two_le_rank` from *Open targets* and `dense_pseudoArcs`, `theorem2_HIC`
  from *Consequences* to the Pacific group; a sub-comment "density lemma, batch 113" lists the 13
  skeleton theorems of items 1–4.
* `axioms.txt` regenerated (`lake env lean Axioms.lean > axioms.txt`): see the counts at the end
  of this report. `sorryAx` occurs in exactly 6 lines: `theorem3_end`, `covering_step`,
  `theorem14`, `fugate_cor1` (open targets) and `theorem15`, `exists_description_covering`
  (consequences). The previous file is kept as `doc/batches/audits/axioms-before-batch113.txt`.

**Counts.** `lake build HPC`: 8299 jobs, success; the only `sorry` warnings are the four remaining
open targets (`theorem3_end`, `covering_step`, `theorem14`, `fugate_cor1`; `Theorem14.lean` gives
two warnings, for `covering_step` and `theorem14`). `axioms.txt`: **309 lines** (296 before:
`- 4` from the open/consequence groups, `+ 17` = the 13 skeleton theorems and the 4 moved
statements in their new groups); `sorryAx` in exactly **6** lines.
`lake build HPCArchive HPCCensus`: 8242 jobs, success; nothing had to change there.
