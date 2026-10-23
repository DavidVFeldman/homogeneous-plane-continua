Commission read: `doc/batches/COMMISSION-batch152.md` (batch 152, Part F, Jones 1949 IV: Whyburn 1939, Theorem 14).

# Report, batch 152

**Outcome.**

| item | outcome |
|---|---|
| A: `whyburn39_moore_curve` | **proved** (shape chosen, recorded at the statement and in §1) |
| B: `whyburn39_curve_from_order_two` | **proved** (shape chosen, recorded at the statement and in §2) |
| C: `whyburn39_local_noncut` | **proved** (statement verbatim; `hx` and `hp` unused) |
| D: `whyburn39_theorem14` | **proved** (statement verbatim) |

Nothing is left open in this batch; `OPEN.md` is not edited.

**Build and axioms.**
* `lake build HPC` succeeds with `import HPC.Jones.Jones49D` at the end of `HPC.lean`.
* No new file contains `sorry` (the word occurs only in the skeleton's module docstring). The only
  warnings in the new files are the two unused hypotheses `hx` and `hp` of `whyburn39_local_noncut`,
  which are kept because the statement is the skeleton's.
* Every theorem of the three new files uses exactly `propext`, `Classical.choice` and `Quot.sound`.
  The audit is `doc/batches/audits/axioms-batch152.txt` (§6 below).
* `axioms.txt` is regenerated from `Axioms.lean` (1183 lines, one per `#print axioms`; 9 new), with `sorryAx` in no line and only standard
  axioms. The previous version is kept as `doc/batches/audits/axioms-before-batch152.txt`
  (1174 lines).
* `Axioms.lean` has the new group *Whyburn 1939 Theorem 14 (batch 152)* (the four items and five
  helpers), after the batch-151 group.

**Uploads.** The commission is at `doc/batches/COMMISSION-batch152.md`; the skeleton is kept verbatim
at `doc/batches/skeletons/Jones49D-batch152.lean`.

**Files.**
* `HPC/Jones/Jones49DSep.lean` (namespace `HPC.Jones.Sec14`): the joining lemma `join_in_domain`
  (Janiszewski's theorem), and `local_join_of_noncut` ((6.22) plus the joining lemma at a non-cut
  point).
* `HPC/Jones/Jones49DCross.lean` (namespace `HPC.Jones.Sec14`): the predicate `BadAt` (Whyburn's
  condition fails at a point), `IsPreconnected.inter_frontier_nonempty'`,
  `not_orderLE_of_accumulating`, and `exists_bad_point_of_crossing` (a bad point at every radius of
  the middle third of a crossing annulus).
* `HPC/Jones/Jones49D.lean`: the skeleton, with every item proved.

**Edits to existing files.** `HPC.lean` (one import), `Axioms.lean`, `axioms.txt`, `README.md`,
`LEDGER.md` §6 (new subsection at the end). No other existing file is touched.

---

## 1. Item A: Moore's curve, replaced by a joining lemma

**What Whyburn uses.** From the curve `C ⊂ J + C_ε` and its region `E ∋ 0`, the proof takes one
thing: a continuum of `R` inside `V_{2ε}(p)` joining `x` and `y` (the arc `x₁wy₁` of `C`, with the
arcs `xx₁`, `yy₁` of `J`). So item A is stated as that connection, with no curve.

**Shape.** `N` is a closed connected subset of the compact `M` with `M − V_ε(p) ⊆ N`, and `W` is the
component of `(N ∪ V_ε(p)ᶜ)ᶜ` containing `p` (Whyburn's `E` up to the choice of base point: an open
set inside `V_ε(p)` whose frontier lies in `N ∪ C_ε`). If `a`, `b` lie in the complementary domain
of `M` containing `x`, and both lie in `W`, then `b` lies in the component of `W ∩ Mᶜ` containing
`a`. This component is open and lies in `R ∩ V_ε(p)`.

**Proof.** Janiszewski's theorem for plane compacta (`HPC.Moore.janiszewski_compact`), applied to
`K = (M ∩ W̄) ∪ N` and `L = Wᶜ ∩ B̄(p, ρ)` with `ρ` so large that `M ⊆ B(p, ρ)`. Here `K ∩ L = N`
(the frontier of `W` lies in `N ∪ C_ε`, and `M ∩ C_ε ⊆ N`), which is connected. `K ⊆ M` does not
separate `a` from `b`, since both lie in one complementary domain of `M`; `L` does not separate them,
since both lie in the connected set `W ⊆ Lᶜ`. Hence `K ∪ L` does not separate them, and the component
of `(K ∪ L)ᶜ` containing `a` and `b` lies in `W` (it misses `L`, and the part of `Wᶜ` outside
`B̄(p, ρ)` is not reached without crossing `L`) and misses `M` (in `W` the points of `M` are in `K`).
So it lies in `W − M`. (In Lean: `HPC.Jones.Sec14.join_in_domain`.)

**Is the boundary of the component a simple closed curve?** Not decided here; it is not needed. The
proof uses neither the Jordan curve theorem nor arcs.

## 2. Item B: the curve `K`, replaced by "no finite order"

**What Whyburn uses.** The curve `K` around `p′` with `K·M = c + d` exists so that the pigeonhole can
run: infinitely many arcs `pᵢqᵢ` enter `D` and leave it. The formalization turns the pigeonhole
around and never builds `K` or `D`.

**Shape.** In a metric space, let `T i` be pairwise disjoint preconnected sets, with points
`b i ∈ T i` converging to `p`, and each `T i` reaching distance `≥ d > 0` from `p`. Then `p` is not
of order `≤ n` for any `n`: the frontier of any small neighbourhood of `p` meets all but finitely
many `T i` (`HPC.Jones.Sec14.not_orderLE_of_accumulating`, using
`IsPreconnected.inter_frontier_nonempty'`).

**The two forms of the commission.** Neither Whyburn's Jordan-curve form (`K·M = c + d`, which needs
`c` and `d` accessible from `Mᶜ`) nor the weaker form with an open `D` is proved or refuted; the
proof of Theorem 14 needs neither.

## 3. Item C: step 3

`whyburn39_local_noncut` is proved with the statement verbatim. `local_join_of_noncut` combines
(6.22) (`whyburn39_6_22_sec14`) and item A: for a non-cut point `p` and `ε > 0` there is `δ > 0` such
that any two points of `R` within `δ` of `p` lie in a connected subset of `R` inside `V_ε(p)`. At
`ε/3` this gives a connected set of diameter `≤ 2ε/3 < ε` joining two terms of the sequence. The
hypotheses `hx` (`x ∉ M`) and `hp` (`p` on the boundary of `R`) are not used: for `x ∈ M` the domain
is empty, and the joining statement holds at every non-cut point of `M`.

## 4. Item D: Theorem 14

`whyburn39_theorem14` is proved with the statement verbatim, without inversion, for bounded and
unbounded `R` alike.

**Route.** Step 4 is reorganized; the limit continuum `H` and the curve `K` are not built.
1. The boundary `B` of `R` is a continuum (`isConnected_frontier_complDomain`) and lies in `M`.
2. If `B` is not locally connected, it is not connected im kleinen at some `P`
   (`locallyConnectedSpace_of_cikAt`), and Moore's p. 236 construction
   (`Sector.exists_crossing_continua_closed`) gives pairwise disjoint subcontinua `tₙ` of `B` crossing
   a square annulus `r₁ ≤ d(·, P) ≤ r₂`.
3. For every `ρ` in the middle third `[r₁ + (r₂ − r₁)/3, r₂ − (r₂ − r₁)/3]`,
   `exists_bad_point_of_crossing` gives `h_ρ ∈ B` with `d(h_ρ, P) = ρ` at which Whyburn's condition
   fails with `ε = (r₂ − r₁)/6` (a sequence of points of `R` converging to `h_ρ`, no two joinable in
   `R` by a connected set of diameter `< ε`), and at which a subsequence of the `tₙ` accumulates.
   This is Moore's sufficiency argument (`moore22_sufficiency_local`), rerun at an arbitrary radius
   `ρ` with `η = (r₂ − r₁)/6`, using the cyclic order (`sector_cyclic`).
4. By item B (in the subspace `M`), `h_ρ` has no finite order in `M`; in particular it is not of
   order 2. By item C, `h_ρ` is a cut point of `M`.
5. The `h_ρ` are distinct (they have distinct distances to `P`), so the cut points of `M` not of
   order 2 are uncountable (`Cardinal.mk_Icc_real`). This contradicts `whyburn_3_2`.

The order of the commission's list ("`moore22_sufficiency_local` and
`isConnected_frontier_complDomain`") is kept in substance: the first enters through
`exists_bad_point_of_crossing`, which contains its argument at a variable radius; it is not called
directly, because its conclusion (local connectedness under the hypothesis everywhere) is the
contrapositive of what step 3 provides only at non-cut points.

## 5. Ledger entries

The new subsection *Jones 1949 IV: Whyburn 1939 Theorem 14 (batch 152)* of `LEDGER.md` §6 quotes each
printed sentence (from page images, pp. 747–748) and records:

| check | place | outcome |
|---|---|---|
| 1 | arc `p₁p₂` in `R` | arcs exist (polygonal arcs, `exists_polyPath_of_isConnected`, `exists_simplePolyArc_of_polyPath`); not used. Harmless |
| 2 | subarc `xy`, finite-cover argument | correct; the sum is only connected (its closure is the continuum), finiteness by uniform continuity unstated. Harmless |
| 3 | "`N` can intersect only one of the arcs" | unargued θ-curve step; true (argument in the ledger); not used. Harmless |
| 4 | the point `0` and the arc `ou` | misprint `ou − o` for `ou − u`; `0` exists because `u` is an interior point of an arc of `J` on the frontier of `I`. Harmless |
| 5 | "the arc `x₁xuyy₁` of `J` is contained in `C`" | unargued, true: the component of `C − C_ε` containing `u` is an arc of `J − C_ε`. Harmless |
| 6 | the limit continuum `H` | `H ⊂ M` (a disc in `R` would join two arcs within `4ε`); nondegenerate (contains `p` and a point of `C_ε`); the `3ε` is a slip (the argument gives `2ε`; any constant works); "every point of `H`" should read "within `V_ε(p)`"; in step 3 `V_{3ε}` is a slip for `V_{2ε}`. Harmless |
| 7 | "there exists points" | misprint for "exist"; the step is correct given `K`. Harmless |
| 8 | the inversion | **counted**: defective proof (gap), theorem true — the fourteenth defective proof of the ledger |

## 6. Axioms per theorem

From `doc/batches/audits/axioms-batch152.txt`:

| theorem | axioms |
|---|---|
| `HPC.Jones.whyburn39_moore_curve` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.whyburn39_curve_from_order_two` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.whyburn39_local_noncut` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.whyburn39_theorem14` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.Sec14.join_in_domain` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.Sec14.local_join_of_noncut` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.Sec14.IsPreconnected.inter_frontier_nonempty'` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.Sec14.not_orderLE_of_accumulating` | `propext`, `Classical.choice`, `Quot.sound` |
| `HPC.Jones.Sec14.exists_bad_point_of_crossing` | `propext`, `Classical.choice`, `Quot.sound` |

The definition `HPC.Jones.Sec14.BadAt` is also printed there.

## 7. Shape changes

* **Item A** (`whyburn39_moore_curve`): the curve `C` and region `E` are replaced by the component `W`
  of `V_ε(p) − N` containing `p`, and the conclusion is the joining property inside `W ∩ Mᶜ`.
* **Item B** (`whyburn39_curve_from_order_two`): the curve `K` is replaced by the statement that a
  point at which infinitely many disjoint connected sets of size `≥ d` accumulate has no finite
  order.
* Items C and D: statements verbatim.

## 8. Reading plan for batch 153: Corollary 1 (p. 749)

"If M is a compact plane semi-locally-connected cyclic continuum, the boundary of every
complementary domain of M is a simple closed curve." Route of REPORT-batch150 §5 (d), with
`B = ∂R`:
1. `B` is a locally connected continuum: `whyburn39_theorem14` and `isConnected_frontier_complDomain`
   (both now available).
2. Every cut point of `B` is a cut point of `M`; `M` is cyclic, so `B` is cyclic. This needs
   arc-accessibility, and `jordan_curve_theorem` (and `tscc_homeomorph_circle` to pass from two arcs
   to a curve homeomorphic to `Circle`).
3. A cyclic locally connected continuum `B` with `B = ∂R` is a simple closed curve: otherwise it
   contains a θ-curve, whose three complementary domains (`HPC/Moore/Sec6Th26.lean`, or
   `jordan_curve_theorem` twice) give a contradiction.
4. `tscc_homeomorph_circle` or `menger_order_two` for the conclusion.

**Ingredient 1: accessibility of boundary points from `R` by arcs.** *Nothing beyond batches 146–152
is needed; one construction is new.* Since `M` is cyclic, no point of `M` cuts `M`, so batch 152's
`HPC.Jones.Sec14.local_join_of_noncut` applies at every boundary point `p`: for every `ε` there is
`δ` such that two points of `R` within `δ` of `p` lie in one component of `W ∩ Mᶜ`, an open
connected subset of `R ∩ V_ε(p)` (`join_in_domain`). Open connected plane sets contain simple
polygonal arcs (`HPC.Plane.exists_polyPath_of_isConnected`, `exists_simplePolyArc_of_polyPath`).
Choosing `xₙ → p` in `R` and polygonal arcs `βₙ` from `xₙ` to `xₙ₊₁` in balls shrinking fast enough
(the radius for `βₙ₊₂` below `d(p, β₀ ∪ … ∪ βₙ)`, possible since each `βₙ` is compact and misses
`p ∈ M`) gives arcs disjoint unless consecutive; Moore's limit-arc construction
`HPC.Moore.exists_tarc_of_seq` (`HPC/Moore/Sec6Lim.lean`) then yields an arc from `x₀` to `p` lying in
`R ∪ {p}`. The new pieces are a bridge from `IsSimplePolyArc` to `TArc` (a simple polygonal arc is an
embedded interval; not in the repository) and the bookkeeping of the radii. The two-sided form of
step 2 also needs one arc in `R` joining the far ends of two accessing arcs, trimmed by
`TArc.first_point`.

**Ingredient 2: a θ-curve in a cyclic Peano continuum that is not a circle.** *This needs more than
batches 146–152 provide.* The repository has arcs only in curves of finite order
(`exists_tarc_of_orderLE`, batch 149), in irreducible continua, and in open plane sets; it does not
have the arc theorem for general Peano continua (Moore–Mazurkiewicz), nor the cyclic-connectivity
theorem (two points of a cyclic Peano continuum lie on a simple closed curve), and `B` is not known
to have finite order. Two ways forward, to be decided in batch 153:
* build the general arc theorem (by `exists_tarc_of_seq` on chains of small connected open sets of
  `B`) and Whyburn's cyclic-connectivity theorem, then add an arc from a point off the curve with a
  first-point trim; or
* avoid the θ-curve inside `B` by working in the plane: use the accessing arcs of ingredient 1 and
  `jordan_curve_theorem` to show directly that every point of `B` has order 2 in `B`, then conclude by
  `menger_order_two`. Whether this second route closes without the arc theorem is not settled here.

`janiszewski_compact`, `plane_unicoherent` and `brouwer_boundary` are available for the separation
steps of both routes.
