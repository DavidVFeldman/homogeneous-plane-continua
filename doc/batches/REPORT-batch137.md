Commission read: `doc/batches/COMMISSION-batch137.md` (batch 137 — Part D, Moore I: F.A. §§2–5 (Theorems 1–19), the bridge to topology, arcs).

# Report, batch 137

`lake build HPC` succeeds with `import HPC.Moore.FA` added at the end of `HPC.lean`. The skeleton is
kept verbatim at `doc/batches/skeletons/MooreFA.lean`; the source is `doc/sources/moore1916.pdf`.
`HPC/Moore/FA.lean` is now an umbrella module importing nine files:

| file | content |
|---|---|
| `Defs.lean` | skeleton §1: Moore's primitives, derived notions, Axioms 1–8 and 5₁ (item A) |
| `Basic.lean` | Theorems 1–9, "`M′` is closed" (item B) |
| `Chains.lean` | Theorem 10 (item B) |
| `Bridge.lean` | the bridge to topology (item D) |
| `Sec4.lean` | Theorems 11–14 (item C), 17–19 (item E) |
| `Thm15.lean` | Theorems 15, 16, Moore's nested-chain construction (item C) |
| `ArcChar.lean` | `isIrreducibleConnected_iff_arc` (item E; Mathlib only) |
| `Arcs.lean` | `isArc_iff` and the unnumbered facts of pp. 139–140 (item E) |
| `Refute.lean` | the printed Theorems 4 and 19 refuted (adjoining `∅` to the regions) |

**Nothing is left open.** Every skeleton `sorry` is proved, in places with a recorded shape change;
four printed statements are refuted, each with a proved corrected form. `rg sorry HPC/Moore` finds
nothing; `OPEN.md` is untouched.

All names below are in namespace `HPC.Moore`; `σ : Space S` is the space.

## Item A — Definitions (skeleton §1)

Kept verbatim from the skeleton, with one forced change. I checked the overbars against the page
image of p. 132: in Axioms 1, 6 and 7, `P̄`, `R̄`, `K̄`, `L̄` are second objects, as the skeleton has
them, not closures.

*Shape change:* Axiom 5₁ (footnote, p. 133: "there exist at least three points") does not involve
the regions. The skeleton's `σ.Axiom5₁` does not typecheck. It is `Space.Axiom5₁ (S := S)`, and the
statements use it in that form.

## Item B — F.A. §3, Theorems 1–10 and "`M′` is closed" (skeleton §2): proved

Each statement carries only the axioms its proof uses. The section heading assumes Axioms 1–3 and
5₁.

| theorem | Lean | Moore's axioms used | remark |
|---|---|---|---|
| 1 | `fa_theorem1` | none | |
| 2 | `fa_theorem2` | 1 | |
| 3 | `fa_theorem3` | 1 | |
| 4 | `fa_theorem4` | 1, 3, 5₁ | *shape:* `hne : R.Nonempty` added (printed form refuted, see below) |
| 5 | `fa_theorem5` | 1, 3, 5₁ | condition (1) `⋂ Rₙ = {P}` checked (ledger item 5) |
| 6 | `fa_theorem6` | 1 | |
| 7 | `fa_theorem7` | 1 | |
| 8 | `fa_theorem8` | 1 | |
| 9 | `fa_theorem9` | 1 | Zermelo's postulate = `Classical.choose` |
| `M′` closed | `fa_cl_isClosed` | none | |
| 10 | `fa_theorem10` | none | proof uses weak chains (see ledger) |

**Refuted:** `not_fa_theorem4_printed` (Theorem 4 for `R = ∅`), in `Refute.lean`. Adjoining `∅`
to the regions (`Space.withEmpty`) changes no derived notion. It preserves Axioms 1–8
(`withEmpty_axiom1` … `withEmpty_axiom8`). At `∅`, Axiom 3 is the connectedness of `S`, which
`isConn_univ` derives from Axioms 1, 3, 4 and 5. The new space has the empty region, which is
finite. So the printed Theorem 4 follows from Axioms 1–8 only if those axioms have no model.

## Item C — F.A. §4, Theorems 11–16 (skeleton §3): proved

| theorem | Lean | Moore's axioms used | remark |
|---|---|---|---|
| 11 | `fa_theorem11` | 1, 4 | |
| 12 | `fa_theorem12` | 1, 4 | |
| 13 | `fa_theorem13` | 1, 4 | |
| 14 | `fa_theorem14` | 1, 4 | *shape:* `hne : ∀ n, (M n).Nonempty`, as in the skeleton |
| 14 printed | `not_fa_theorem14_printed` | 1 | refuted with every `Mₙ = ∅` |
| 15 | `fa_theorem15` | 1, 2, 3, 4, 5₁ | Moore's construction by nested simple chains |
| 16 | `fa_theorem16` | 1, 2, 3, 4, 5₁ | "without `R`" = `σ.ext R` |

*Shape change (Theorems 15, 16):* the hypothesis is Axiom 5₁ instead of Axiom 5. 5₁ is weaker
(`axiom5₁_of_axiom5`). Axioms 3 and 5₁ enter only through metrizability.

**Theorem 15 follows Moore's construction (pp. 136–139).** The core is `exists_irreducible` in
`Thm15.lean`. It builds:

* a sequence of simple chains `Cₙ` from `A` to `B` in the domain;
* with each link of `Cₙ₊₁`, closure included, in a link of `Cₙ`, and the owners monotone
  (`exists_refine`, `exists_chains`);
* with `C` the intersection of the closures of the unions (`moore_isPreconnected_iInter`).

From the chains it follows that `C` is an irreducible continuum from `A` to `B`. The arc
characterization then converts this into Moore's arc (`isArc_iff_topological`).

*Shape change (smallness):* Moore uses the regions `Kₙ, Kₙ₊₁, …` of Theorem 5 to make the links
small. The formal proof requires instead that the links of `Cₙ` have diameter `< 2/(n+1)` for a
compatible metric (from `metrizable`). The two do the same job.

Part III of the proof needs three arguments that Moore does not print. All three are supplied (ledger
item 7):

* "Furthermore it is clear that …";
* "It is clear that `S_A` contains `A`";
* a further gap: "`P_B` precedes `P`" fails at stage `n` unless `n` is large enough that the links of
  `P_A` and of `P` do not meet.

## Item D — The bridge (skeleton §4): proved

`σ.topology` is the topology generated by the regions.

| statement | Lean | Moore's axioms used |
|---|---|---|
| regions are open | `isOpen_region` | none |
| regions form a basis | `isTopologicalBasis_region` | 1 |
| limit point = `AccPt` | `isLimitPt_iff` | 1 |
| `M′` = closure | `cl_eq_closure` | 1 |
| closed = `IsClosed` | `isClosedM_iff` | 1 |
| connected = `IsPreconnected` | `isConn_iff` | 1 |
| domain = open + preconnected | `isDomain_iff` | 1 |
| Heine–Borel = `IsCompact` | `heineBorel_iff` | none |
| T1, regular, T2 | `t1Space`, `regularSpace`, `t2Space` | 1 |
| second countable | `secondCountable` | 1, 3, 5₁ (the fundamental regions of Axiom 3, via Theorem 5) |
| metrizable | `metrizable` | 1, 3, 5₁ (Urysohn) |
| closures of regions compact, bounded ⇔ relatively compact | `isCompact_closure_region`, `isCompact_closure_of_isBoundedM`, `isBoundedM_of_isCompact` | 1, 4 |

Answer to "if some identification needs more axioms, say which": none of the identifications
(limit point, closed, connected, Heine–Borel, closure) needs more than Axiom 1. Metrizability needs
Axioms 1, 3 and 5₁, and Axiom 2 is not used. The section heading (1–4, 5₁) is enough for everything.

## Item E — Arcs (skeleton §5): proved, with one printed statement refuted

* `isIrreducibleConnected_iff_arc` (`ArcChar.lean`): in a metrizable space, an irreducible
  continuum from `A ≠ B` is exactly an embedded `[0, 1]` from `A` to `B`. It uses Mathlib only
  (none of Moore's axioms). The proof is the standard one: non-cut points, the order on an
  irreducible continuum, and a separable dense order that yields `[0, 1]`.
* `isArc_iff`: a Moore arc is an embedded `[0, 1]`. Axioms 1, 3, 4, 5₁. Also
  `isArc_iff_topological` (Axioms 1, 4) and `Space.IsArc.union` (Axioms 1, 4).
* The unnumbered facts of pp. 139–140, each as its own lemma (Axioms 1, 3, 4, 5₁):

| fact | Lean | status |
|---|---|---|
| splitting an arc at a point | `fa_sec5_arc_split` | proved |
| the unique interval `XY` | `fa_sec5_interval_unique` | proved (`∃!`) |
| first and last points on a closed set | `fa_sec5_first_point`, `fa_sec5_last_point` | proved; *shape:* "between `P₁` and `B`" read as "on the interval `P₁B`" |
| limit points along an arc | `fa_sec5_limitPt_iff` | proved; *shape:* an interval may end at `P` when `P` is `A` or `B` |
| the same, as printed | `not_fa_sec5_limitPt_printed` | **refuted** (fails for `P = A`) |
| two arcs between two points of a simple closed curve | `fa_scc_two_arcs` | proved, including uniqueness of the two arcs |

* Theorems 17–19 (`Sec4.lean`):

| theorem | Lean | Moore's axioms used |
|---|---|---|
| 17 | `fa_theorem17` | 1, 4, 5 |
| 18 | `fa_theorem18` | 1, 4, 5 |
| 19 | `fa_theorem19` | 1, 3, 4, 5; *shape:* `hne : R.Nonempty` |
| 19 printed | `not_fa_theorem19_printed` | refuted for `R = ∅` (as for Theorem 4) |

## Ledger entries (`LEDGER.md` §6, new subsection "Moore 1916 … F.A. §§2–5 (batch 137)")

* **Refuted as printed:**
  * Theorem 14 without "`Mₙ` nonempty";
  * Theorems 4 and 19 for `R = ∅`;
  * the limit-point characterization on an arc (p. 139), at an endpoint.
* **Reworded, not refuted:**
  * first and last points ("between" → "on the interval");
  * Theorem 10 (Moore's chain `R₁ ⋯ R_k R` need not be simple, so a shortest sub-chain is taken:
    `exists_simpleChain_sublist`).
* **Checks of commission §3:**
  1. Connected: the nonempty-parts reading is needed (with `∅` allowed, no nonempty set is
     connected).
  2. Theorem 1: no axiom, confirmed.
  3. Unproved statements: what each proof needs is recorded. Theorem 17 uses exactly Axiom 5 and
     Theorem 13, as Moore says.
  4. Theorem 14: refuted as printed.
  5. Theorem 5 (1): confirmed (from (3) and Theorem 3; Theorem 4 is needed for the construction).
  6. Zermelo: noted.
  7. Theorem 15 part III: the two "clear" steps are supplied, and a third gap is found and filled.
  8. Theorem 16: confirmed. The exterior is a domain (open since `R′` is closed, connected by
     Axiom 3).
  9. §6's first sentence: partly borne out. Axiom 1 (2) with closures is used directly in
     Theorem 4 and in regularity. The printed Theorem 5 (3) lacks the closure, but the skeleton's
     form supplies it.
* **Remarks:**
  * Axiom 5₁ typing;
  * 5₁ in place of 5 in Theorems 15, 16 and the arc results;
  * Lennes's Theorems 2–9 proved via the arc characterization.

## Axioms (Lean)

`doc/batches/audits/axioms-batch137.txt` is the `#print axioms` output for all 139 new theorems
(source `axioms-batch137.lean`). Every theorem depends only on standard axioms, a subset of
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` appears nowhere. `axioms.txt` was
regenerated with the new group "Moore F.A. §§2–5 (batch 137)" (54 main results). It went from 796
to 850 lines, with no existing line changed, and `sorryAx` appears in no line.
The batch-136 version is kept as `doc/batches/audits/axioms-before-batch137.txt`.

## Other edits

* The stale docstrings of `HPC/Jones/Jones51.lean` and `HPC/Jones/Jones48.lean` (authorized) now
  say that Jones 1951 Theorem 1 is proved in batch 136 (`jones51_theorem1`).
* `README.md`:
  * a Part D line for Moore F.A. §§2–5;
  * the batch count (137);
  * the `HPC/Moore` and `HPC/Jones` rows;
  * the `doc/sources/` row.

## What batch 138 (F.A. §6, Theorems 20–35) needs from this one

* **The bridge:**
  * `cl_eq_closure`, `isClosedM_iff`, `isConn_iff`, `isDomain_iff`, `heineBorel_iff`,
    `isLimitPt_iff`;
  * `metrizable`, `secondCountable`, `t2Space`, `regularSpace`.

  These let §6's arguments about separation and domains run in Mathlib's topology. Note that the
  identifications need only Axiom 1, and metrizability needs 1, 3, 5₁.
* **Arcs:**
  * `isArc_iff`, `isArc_iff_topological`, `Space.IsArc.union`;
  * `fa_sec5_arc_split`, `fa_sec5_interval_unique`, `fa_sec5_first_point`, `fa_sec5_last_point`,
    `fa_sec5_limitPt_iff`;
  * `fa_scc_two_arcs`.

  §6 builds simple closed curves out of arcs and splits them, and these are the pieces it uses.
* **Theorems 15 and 16:** `fa_theorem15`, `fa_theorem16`, which give arcs in domains and in
  exteriors.
* **Theorems 13, 14, 17, 18:** for compactness arguments.
* **New axioms:** §6 brings in Axioms 6–8 (`Defs.lean`, verbatim). None of them is used in this
  batch, except in the refutations, which check that adjoining `∅` preserves them.
* **To watch:** degenerate cases like those refuted here (empty regions, arcs at their endpoints).
  They may recur in §6's statements, which should carry nonemptiness where the proofs assume a
  point.
