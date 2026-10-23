Commission read: COMMISSION-batch125.md (batch 125 — `jct` part I (crossing parity); Theorem 4 as printed for `k ≥ 4`).

# Report, batch 125

**Outcome.**

| item | verdict |
|---|---|
| 1.1 single-edge facts (`crossesEast_comm`, `not_crossesEast_of_mem`, `crossesEast_locallyConstant_of_ne`) | **proved** |
| 1.2 the vertex rule | **proved**, as `crossesEast_jump` + `sum_vJump_telescope` (statement below) |
| 1.3 `parity_locallyConstant`, `parity_eq_of_isPreconnected` | **proved**, for every closed polygon (simplicity dropped) |
| 1.4 `parity_far`, `parity_eq_zero_of_far` | **proved** (no simplicity) |
| 1.5 `exists_parity_flip`, `exists_nonhorizontal_edge`, `polygon_separates` | **proved** |
| 2. Theorem 4 as printed, `k ≥ 4` (`theorem4_literal_ge4`, `theorem4LiteralGe4_holds`) | **proved**; `Theorem4LiteralGe4` closes (OPEN item 2 → closed items) |

Build: `lake build HPC` succeeds. No new `sorry`. `axioms.txt` regenerated (498 lines); `sorryAx`
occurs in **one line**, `HPC.Plane.fugate_cor1` (unchanged). Every other line shows
`[propext, Classical.choice, Quot.sound]` or a subset. Per-batch audit:
`doc/batches/audits/axioms-batch125.{lean,txt}` (all 52 theorems of the two new files, plus
`fugate_cor1`; a copy of the output is `axioms-batch125.txt` at the root); the previous
`axioms.txt` is saved as `doc/batches/audits/axioms-before-batch125.txt`.

Files:

* `HPC/Plane/Jct1.lean` — the commissioned skeleton, every `sorry` replaced by a proof;
* `HPC/Fold/Theorem4Ge4.lean` — new: the model construction for item 2 and its transfer to chains;
* edited as allowed: `HPC.lean` (`import HPC.Plane.Jct1` at the end), `Axioms.lean` (group
  "Jordan curve theorem for polygons (batch 125)" and four lines in the Bing 1948 group under
  Theorem 4), `axioms.txt`, `OPEN.md`, `README.md`, `LEDGER.md` (item 2 closed).

**Changes of shape** (all recorded in the header of `Jct1.lean`):

* `vertex_rule_placeholder` deleted (replaced by the two lemmas below);
* `hv : IsSimpleVertices v` dropped from `parity_locallyConstant`, `parity_eq_of_isPreconnected`,
  `parity_eq_zero_of_far` (they hold for every closed polygon `v : Fin n → Pt`, any `n`); the
  statements are otherwise as in the skeleton;
* the import `HPC.Fold.Theorem4Only` of the skeleton is replaced by `HPC.Fold.Theorem4Ge4`, which
  imports it; `theorem4_literal_ge4` is the term `theorem4_literal_ge4_model …`.

---

## 1. `jct`, part I

### The vertex rule actually proved

With `ceInd x a b ∈ ZMod 2` the indicator of `CrossesEast x a b` and
`vJump x w = 1` iff `w.2 = x.2 ∧ x.1 < w.1` (the vertex `w` has the height of `x` and lies strictly
to its right):

```
theorem crossesEast_jump {x a b : Pt} (hx : x ∉ segment ℝ a b) :
    ∀ᶠ y in 𝓝 x, (x.2 ≤ y.2 → (CrossesEast y a b ↔ CrossesEast x a b)) ∧
      (y.2 < x.2 → ceInd y a b + ceInd x a b = vJump x a + vJump x b)

theorem sum_vJump_telescope {n : ℕ} (v : Fin n → Pt) (x : Pt) :
    ∑ i : Fin n, (vJump x (v i) + vJump x (v ⟨(i.val + 1) % n, _⟩)) = 0
```

That is: per edge, near any point `x` off the edge, the indicator does not change at points not
below `x` (the half-open rule puts height `x.2` with the points above), and it jumps by a sum of
two *vertex* terms at points below `x`. Around a closed polygon each vertex is an end of two edges,
so the jumps cancel mod 2 (`finRotate` reindexing). Horizontal edges need no separate treatment:
they are never counted, and if one lies at the height of `x`, its two ends are on the same side of
`x` (as `x` is off it), so its jump `vJump x a + vJump x b` is `0`. This is the "maximal horizontal
runs" rule of the commission in local form: the run's interior vertices contribute twice, and only
the vertices bounding the run against non-horizontal edges remain. It needs neither simplicity nor
`n ≥ 3`.

Proof of `crossesEast_jump`: `CrossesEast y a b ↔ Xor' (a.2 ≤ y.2) (b.2 ≤ y.2) ∧ 0 < F y` with
`F y = a.1 + (y.2 − a.2)·c − y.1` continuous (`crossesEast_iff_xor`); near `x` the atoms
`a.2 ≤ y.2` (for `a.2 ≠ x.2`) and the sign of `F` (when `F x ≠ 0`) are constant. Three cases: no end
at height `x.2` (`F x ≠ 0` whenever the straddle holds, else `x` is on the segment,
`mem_segment_of_straddle`); both ends (horizontal, `mem_segment_of_horizontal`); exactly one end
(`crossesEast_jump_end`, where `F x = a.1 − x.1 ≠ 0`; the other case by `crossesEast_comm`).

### The rest

* `parity_locallyConstant` (from `parity_eventually_eq`): sum the per-edge statements
  (`Filter.eventually_all`); above or at height `x.2` the sums agree term by term, below they differ
  by `sum_vJump_telescope = 0`.
* `parity_eq_of_isPreconnected`: `IsPreconnected.constant_of_mapsTo` for `ZMod.val ∘ parity v`
  into the discrete `ℕ`.
* `parity_far`: `R = ∑ |(v i).1|`; a crossed edge's crossing point lies on the edge, hence left of
  `R`. `parity_eq_zero_of_far`: the polygon lies in the sup-ball of radius `∑ ‖v i‖`; outside the
  ball of radius `max R₀ R₁` (connected, `isConnected_compl_closedBall_pt`) parity is constant and
  equals its value at `(|R₀| + |R₁| + 1, 0)`, which is `0`.
* `exists_parity_flip`: `p` is the point of edge `i` at a height `c` strictly between the heights of
  its ends and different from the height of every vertex (`Set.Ioo_infinite`, a finite set of
  heights). Then `p` is no vertex, so by simplicity it lies on no other edge
  (`not_mem_polyEdge_of_ne`); the other edges' indicators are locally constant at `p`
  (`ceInd_eventually_eq`, no end at height `c`); edge `i` is crossed from `(p.1 − t, c)` and not
  from `(p.1 + t, c)`; neither point is on edge `i` (on a non-horizontal segment the abscissa is a
  function of the height, `fst_eq_of_mem_segment`).
* `exists_nonhorizontal_edge`: otherwise all vertices have one height; at the leftmost vertex `v m`
  the midpoint of `v m` and its nearer neighbour lies on both edges at `v m` and is none of
  `v (m−1), v m`, contradicting the adjacent-edge clause of `IsSimpleVertices` for the pair
  `(m − 1, m)`.
* `polygon_separates`: the two parity sets are open (`isOpen_parity_set`, the polygon is closed);
  one of the two points of `exists_parity_flip` has parity `1`; the odd set lies in the ball of
  `parity_eq_zero_of_far'`; if `Γᶜ` were connected the two points would have equal parity.

### Notes for part II

* The same vertex-jump calculus gives the flip across **horizontal** edges directly, without strips:
  for `p` interior to a horizontal edge `e` at height `h` and not a vertex, compare `p + (0, t)` and
  `p − (0, t)`. Every edge without an end at height `h` keeps its indicator. The others contribute
  the vertex terms of the vertices at height `h` right of `p`, each counted once per non-horizontal
  edge at it, i.e. `2 − #(horizontal edges at it)`. Mod 2 this is the number of horizontal edges at
  height `h` with exactly one end right of `p`. By simplicity the only such edge is `e` itself
  (another one would contain `p`), so the parity flips. A uniform statement "parity flips across
  every edge at every non-vertex point" is therefore within reach of `crossesEast_jump`, in its
  form for a point lying on exactly one (horizontal) edge. This gives `frontier ⊇ Γ` for both
  parity sets, and the flip lemma can then be stated for every edge.
* For the connectedness of each parity set the one-sided strips along `Γ` are still needed. The
  local constancy above only gives "constant on preconnected sets".
* `exists_parity_flip` already gives, at a generic point of every non-horizontal edge, a
  neighbourhood in which `Γ` is the edge and the two sides have different parities. This is the
  local picture the strips are made of.

---

## 2. Theorem 4 as printed, `k ≥ 4` — proved

**Statement** (`HPC.Fold.theorem4_literal_ge4`, `HPC/Plane/Jct1.lean`; proof
`HPC.Fold.theorem4_literal_ge4_model`, `HPC/Fold/Theorem4Ge4.lean`): exactly the commissioned one.
`theorem4LiteralGe4_holds : Theorem4LiteralGe4`.

**Model** (`HPC.Fold.Recon123`, `Theorem4Ge4.lean`). `two_modelZ`: for `K ≥ 4` and `r ≤ s` with a
link in `[r, s]` meeting level `0` and one meeting level `K − 1`, there is `β` with `β r = 0`,
`β s` maximal, `PCons`, and the condition `OnlyM` at `r` and at `s`, where `OnlyM β i` is the
disjunction of:

1. a neighbour of `i` is in the block of `i` (→ `onlyIn_of_neighbour`, batch 123);
2. no neighbour of `i` shares a coarse link with `i` (→ `onlyIn_of_no_common`, batch 124);
3. `OnlyE`: some coarse link `e_j` met by `d_i` can be met by no neighbour of `i` lying in another
   block (→ new, `onlyIn_of_meet`: a point of `d_i ∩ e_j` would lie in such a neighbour, by
   `link_subset_neighbours`).

`onlyIn_of_onlyM` turns `OnlyM` into `OnlyIn` for chains.

**The construction** (`two_coreZ`, for `d_h` meeting `e₁` before `d_k` meeting `e_m`; the other order
by mirroring, `OnlyM.of_flip`). It is batch 123's `two_core` with three changes:

* **Pair form at both ends.** `H` is Theorem 3 in the pair form on `D(1, h)` with `{d_r, d_{r'}}` in
  the first block, and `G` likewise on `D(k, n)` with `{d_s, d_{s'}}` (`seg3Z`, from `pair_main`
  and `BConclZ.sub_abs`). Here `r'` is a neighbour of `r` sharing a coarse link (if any, and if
  `r < h`), otherwise `r` itself; the same for `s'`. Then `F r' = 0` and `F s' = F s`, as for `r`,
  `s` in `two_core`.
* **The new grouping.** The middle groups are `genG`, except that the whole `G`-block of `d_k` goes
  to the top group `K − 3`. For `K ≥ 5` this changes nothing, since that block lies in
  `e_{m−1} + e_m`. For `K = 4` it is needed: a link with coarse interval `[1, 2]` has `genG = 0`,
  and next to the `G`-part it would jump by two. `genG_lip` and `genWin_spec` hold for `K ≥ 4`
  (`genG_lip4`, `genWin_spec4`).
* **The case where the companion would leave the segment** (`r = h` and `r' = h + 1`, resp.
  `s = k` and `s' = k − 1`). This is the place the report of batch 124 pointed at, and the place
  where the two companions can coincide (`K = 4`, `s = r + 2`). Here no companion is used. At
  `r = h` (which meets `e₁`) the time of `r` is `0`, and a neighbour at non-zero time has
  `g ≠ 0`, hence lies in `e₃` or higher (`σ ≥ 2`), so it cannot meet `e₁`: this is `OnlyE` with
  `j = 0`. Symmetrically, at `s = k` a neighbour not at the top time has `ρ < K − 2` and cannot
  meet `e_m` (`OnlyE` with `j = K − 1`).

Every step is formal. Nothing beyond the batch-122/123/124 model is assumed, and there is no case
split on `K = 4` versus `K ≥ 5`.

Ledger: the batch-124 row (`Theorem4LiteralND`, `m = 3`, `r < s`) now records that the statement as
printed is proved for `m ≥ 4`. The degenerate row is updated the same way.

---

## 3. Deliverables / not attempted

* `axioms.txt` regenerated; `axioms-batch125.txt` (root, and `doc/batches/audits/`) is the output
  of `doc/batches/audits/axioms-batch125.lean`.
* Not attempted, as commissioned: part II of `jct`, `enclose`, `janiszewski`, `fugate_cor1`,
  `treeLike_nonseparating`.
