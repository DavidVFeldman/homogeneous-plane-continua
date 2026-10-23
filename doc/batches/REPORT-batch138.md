Commission read: `doc/batches/COMMISSION-batch138.md` (batch 138 — Part D, Moore II: F.A. §6, Theorems 20–34).

# Report, batch 138

`lake build HPC` succeeds with `import HPC.Moore.FA6` added at the end of `HPC.lean`. The skeleton is
kept verbatim at `doc/batches/skeletons/MooreFA6.lean` (the commission is at
`doc/batches/COMMISSION-batch138.md`); the source is `doc/sources/moore1916.pdf`, pp. 140–150.
`HPC/Moore/FA6.lean` is an umbrella module (with a table in its docstring) importing the files
below; the skeleton's text is distributed over them.

| file | content |
|---|---|
| `Sec6Defs.lean` | skeleton §1: `openArc`, `IsInteriorOf`, `SeparatesOn`, `InOrder` (verbatim, item A) |
| `Sec6Arc.lean`, `Sec6Plane.lean` | arcs and closed curves in a topological space (`Gen.TArc`, `Gen.TSCC`), sub-arcs, first points, gluing; `Gen.exists_access`, `Gen.exists_cross` (reaching a boundary through an open set) |
| `Sec6A.lean` | the bridge for §6 (boundary = frontier, exterior = complement of closure, local connectedness, arc-connectedness); Theorems 20–23; `existsUnique_interior`; Theorem 23 as printed refuted |
| `Sec6Th24.lean` … `Sec6Th27.lean`, `Sec6B.lean` | Theorems 24–27 (topological versions `Gen.th24_*`, `Gen.th25`, `Gen.th26`, `Gen.th27`, and the Moore-space statements) |
| `Sec6Th28.lean` | Theorem 28 |
| `Sec6Th29.lean` | Theorems 29, 30 |
| `Sec6Th31.lean` | Theorem 31 (`th31_pocket`, order lemmas on arcs) |
| `Sec6Lim.lean` | limit arcs: `Gen.tarc_of_seq`, `Gen.exists_tarc_of_seq` |
| `Sec6Th32.lean` | Theorem 32 (`sides`, `side_propagate`, `accessible`) |
| `Sec6Th33.lean` | Theorems 33, 34 and 34 for any region (Kline's proof) |

**Nothing is left open.** Every skeleton `sorry` is proved, in places with a recorded shape
change. One printed statement (Theorem 23) is refuted, with the corrected form proved. One
statement (Theorem 32) gets an added hypothesis whose necessity is argued but not formally refuted.
`rg sorry HPC/Moore` finds nothing; `OPEN.md` is untouched.

All names below are in namespace `HPC.Moore`; `σ : Space S` is the space. "Axioms used" means
Moore's axioms, which are explicit hypotheses of every statement (the skeleton's section assumes
Axioms 1–8; each statement keeps only those its proof uses). The method throughout: Moore's
notions are translated to topology by the batch-137 bridge (the regions form a basis of a
metrizable, locally connected, arc-connected, non-compact topology in which closures of regions
are compact), the argument is carried out on embedded `[0, 1]`'s, and the result is translated back.

## Item A — Conventions (skeleton header and §1)

* `openArc A B K = K − {A, B}` (Moore's underlined arc), `IsInteriorOf J R` ("`R` is a region whose
  boundary is `J`"), `SeparatesOn`, `InOrder` — kept verbatim from the skeleton. `InOrder` uses the
  batch-137 parametrization (`isArc_iff`); the proofs work with it through `Gen.order_of_arc_sub`
  and `Gen.image_Icc_subset_of_arc` (`Sec6Th31.lean`). No change.
* **`existsUnique_interior`** (proved; Axioms 1, 3, 4, 5, 7, 8): every closed curve has exactly
  one interior. Existence is Axiom 8, uniqueness Theorem 21 applied in both directions. **Recorded
  as an unnumbered gap** (ledger check 1).

## Item B — Theorems 20–34 (skeleton §2): all proved

| theorem | Lean | Moore's axioms used | status / remark |
|---|---|---|---|
| 20 | `fa_theorem20` | 7 | proved; no proof printed ("easily … Axiom 7") — supplied, uses only Axiom 7 |
| 21 | `fa_theorem21` | 1, 3, 4, 5, 7 | proved, Moore's proof |
| 22 | `fa_theorem22` | 1, 3, 4, 5 | proved; no proof printed — batch 137's `isConn_univ`, not Moore's hint |
| — | `existsUnique_interior` | 1, 3, 4, 5, 7, 8 | proved (item A) |
| 23 | `fa_theorem23` | 1, 2, 3, 4, 5₁, 8 | proved, Moore's proof; *shape:* `hne : R.Nonempty` added |
| 23 printed | `not_fa_theorem23_printed` | 1–8 | **refuted** (empty region, `withEmpty`) |
| 24 | `fa_theorem24` | 1, 2, 3, 4, 5, 7 | proved, Moore's proof; *shape:* the hypothesis "`AXB` is an arc" dropped (unused) |
| 25 | `fa_theorem25` | 1, 2, 3, 4, 5, 7, 8 | proved, Moore's proof with three steps supplied |
| 26 | `fa_theorem26` | 1, 2, 3, 4, 5, 7, 8 | proved, Moore's proof simplified (his Case I reduced to the others) |
| 27 | `fa_theorem27` | 1, 2, 3, 4, 5, 7, 8 | proved, Moore's proof |
| 28 | `fa_theorem28` | 1, 2, 3, 4, 5₁, 6, 7 | proved, Moore's proof with one step corrected; *shape:* conclusion strengthened to `O ∈ openArc A B C₁` |
| 29 | `fa_theorem29` | 1, 2, 3, 4, 5, 7, 8 | proved, Moore's proof (Case I: Theorems 24, 25; Case II: Theorem 27) |
| 30 | `fa_theorem30` | 1, 2, 3, 4, 5, 7, 8 | proved; no proof printed — supplied; *shape:* `B ∈ DBC` dropped (holds for either arc of `J` from `D` to `C`) |
| 31 | `fa_theorem31` | 1–8 | proved, Moore's proof; tacit hypothesis `B ≠ C, D` (already in the skeleton) |
| 32 | `fa_theorem32` | 1–8 | proved; *shape:* `hRK : Disjoint R K` **added**, several hypotheses dropped (below) |
| 33 | `fa_theorem33` | 1–8 | proved, Kline's proof (p. 150) |
| 34 | `fa_theorem34` | 1–8 | proved (closed-curve form; printed "Jordan arc" is a misprint) |
| 34, any region | `fa_theorem34_region` | 1–8 | proved, Kline's proof, with a gap filled |

Every statement's axioms are made explicit; this is a shape change throughout and is recorded in
each docstring. Where Axiom 5₁ appears, it replaces Axiom 5 (weaker, `axiom5₁_of_axiom5`).

**Notes on individual theorems.**

* **20.** For a region `R̄` about the boundary point `P`, Axiom 7 gives a region `L ⊆ R̄` in the
  exterior and a region `L̄ ∋ P` in which every boundary point of `R` is a boundary point of `L`;
  so `L̄` contains a point of `L`.
* **21.** Moore's proof, with "Theorem 18" read as: `R′` is compact (Axiom 4), `S` is not (Axiom 5).
* **23.** `A₁`, `B₁` are obtained by first-point arguments on the parametrized arc; the region of
  Moore's last step lies in the interval `A₁OB₁` because it misses `AA₁ + B₁B`.
* **24.** Only that `AXBCA`, `AXBDA` have interiors and that the open arc `AXB` lies in `R` is used.
* **25.** Supplied: the three-set decomposition `R − AXB = R₁ + R₂ + Y` with `Y` open (Moore: "It is
  clear …"), the arc `FH` (`Gen.exists_cross`, aimed at interior points of `AXB`, since Moore's
  choice "`H` near `A`" can land on `ACB`), and `EL − L ⊆ Y`.
* **26.** `Y` (points without all three curves) is nonempty by Theorems 17, 13 (compactness); Moore's
  Case I (which used Theorem 25) is reduced to Cases II and III, so his auxiliary curves `J̄₁`, `J̄₂`
  are not needed.
* **28.** Moore: "The point-set `A₂C + CP + PD + DB₂` contains as a subset an arc `AXB` satisfying
  conditions (1), (2), and (3)." The arc `CA₂` runs in `R_A`, which straddles `J`, so this needs a
  correction: `A` is taken as the first point of `CA₂` outside `M`, which lies on `J`, hence on the
  open arc `A₁O`. The point `P` is not needed. Both Axioms 6 and 7 are hypotheses since `M` may be
  the interior or the exterior.
* **30.** Proof supplied (`Gen.th30`). Case I (both open arcs within `J`): near a point `Q` of
  `ADB` on the chosen arc `DBC`, Theorems 24, 25 locate points of both interiors. Case II (both
  without): the four combinations of Theorem 27's alternatives for `AXB` and `CYD`, each closed by
  Theorems 24–27 and 20.
* **31.** Moore's five steps (the closed curve `J₀` of Theorem 23's construction; Theorem 28 twice;
  Theorem 27, which supplies the "`E₂BG₂` within `R₃`" that Moore's appeal to Theorem 25 needs;
  Theorem 24 (3)). `th31_pocket` packages steps 1–4 and also records that the two interiors miss
  the arc, which Theorem 32 uses.
* **32.** *Shape (check 4).* Added: `R` has no point in common with `AB`. Dropped (unused): `X₁ ⊆ H`,
  the arc hypotheses on `A₁X₁B₁` and on the segment `A₁DB₁`, `X₁ ∩ K`, and `IsArc A B K` (implied
  by the order hypothesis). Kept: `H` a domain, `AB ⊆ H`, the order `A A₁ D B₁ B`, `D` on the
  boundary curve, `R ⊆ H`, `C ∈ R`. Proof: Moore's covering by chains of Theorem-31 pockets
  (`sides`), with his Class I/II least-upper-bound argument replaced by connectedness of an interval
  (`side_propagate`), dependent choice for the infinite chain, and the limit arc `τ` by
  `Gen.exists_tarc_of_seq` (compact + connected + irreducible ⇒ arc, by batch 137's
  `isIrreducibleConnected_iff_arc`). The general statement proved is `accessible`: in an open set `O`
  containing the arc near its end `B`, every point of a component `Q` of `O − AB` having a point of
  the open arc as a limit point is joined to `B` by an arc lying in `Q + B`.
* **33, 34.** Kline's general proof (p. 150) is formalized; Moore's first proof (pp. 148–150, for
  regions bounded by closed curves) is not needed. `reach_end` is Kline's "By Theorems 31 and 32,
  some point `F` on `XA` can be joined to `A` …". **Gap filled in Kline's proof:** the first point of
  `DC` on `CAB` may be the end `B`; then `C` and `D` are joined around the arc `C … A B … D` (`joinZ`).

## Ledger entries (`LEDGER.md` §6, new subsection "Moore 1916, F.A., §6, Theorems 20–34 (batch 138)")

* **Refuted as printed:** Theorem 23 for the empty region (`not_fa_theorem23_printed`).
* **Hypothesis added, literal form not formally refuted:** Theorem 32 (`R` disjoint from `AB`).
* **Checks of commission §3** (each with the printed sentence quoted in the ledger):
  1. Interior of a closed curve: undefined in F.A.; `existsUnique_interior` fills the gap.
  2. Theorem 23: refuted for `R = ∅`; `hne` added.
  3. Theorem 31: `B ≠ C, D` is a tacit hypothesis. The endpoint case was not pursued: no later
     theorem uses it (Theorem 32 applies Theorem 31 only at interior points of the arc).
  4. Theorem 32: the intended hypotheses are `AB ⊆ H` and `R ⊆ H` (not `A₁X₁B₁ ⊆ H`), plus `R`
     disjoint from `AB`. Without the last, a point `C` of `AA₁` inside `R` (the interval `AA₁` can
     enter `R`) defeats the conclusion, since `C` itself is on `AB`. Not formally refuted: that
     would need a model of Axioms 1–8 (the plane), which the repository does not have.
  5. Theorem 33: read as `R − (AB − A)` (Moore's own last line has it so). The general (Kline)
     proof is formalized; the special one is not needed.
  6. Theorem 34: "Jordan arc" is a misprint for closed curve. Both `fa_theorem34` and
     `fa_theorem34_region` are proved; the second gives the first.
  7. Unargued steps: supplied for Theorems 23, 25, 26, 28 (corrected), 32 (limit arc and the
     infinite chain); Theorem 33's "case where `P₁` or `P₂` is on `DE`" and Theorem 34's "It easily
     follows that `R − AB` is connected" are moot (special proof not used); Kline's proof has a
     gap, filled (`joinZ`).
  8. Degenerate cases: Theorem 23 (empty region); Theorem 28 (`O` in the open arc, stated);
     Theorem 30 (`B ∈ DBC` unnecessary); Theorem 31 (`B` an endpoint); Theorem 32 (`C` on `AB`);
     Theorem 34 (first point at the end `B`).
* **Correction (§0):** batch-137 check 9 now quotes the printed Theorem 5 (3) with the prime,
  "`R′ₙ` is a subset of `R`", and says the skeleton's form is the printed form.

## Axioms (Lean)

`doc/batches/audits/axioms-batch138.txt` is the `#print axioms` output for all 103 new theorems
(source `axioms-batch138.lean`, listing every theorem of the fifteen new files). Every theorem
depends only on standard axioms, a subset of `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx` appears nowhere. `axioms.txt` was regenerated with the new group "Moore F.A. §6 (batch
138)" (32 main results). It went from 850 to 882 lines, with no existing line changed, and
`sorryAx` appears in no line. The batch-137 version is kept as
`doc/batches/audits/axioms-before-batch138.txt`.

## Other edits

* `HPC.lean`: `import HPC.Moore.FA6`.
* `README.md`: a Part D line for Moore F.A. §6; the batch count (138); the `HPC/Moore` row (§§2–6).
* `LEDGER.md` §6: the new subsection, and the batch-137 check 9 correction.

## What batch 139 (F.A. §7, Theorems 35–43, pp. 150–157) needs from this one

§7 is headed "Consequences of Axioms 2–5, 8 and Theorems 5, 15, 20, 33, and 34". Read against the
proofs:

| theorem | statement (short) | §6 results its printed proof cites |
|---|---|---|
| 35 | every region contains a closed curve | 23, 34 (with 4, 15, 16) |
| 36 | a closed curve in `R` enclosing a given point `O` of `R` | 34, 33, 27, 21, 20 (with 4, 19, 35, Axiom 1) |
| 37 | arcs of `C` within `J` near `O`: extreme points `O₁`, `O₂` | 29 (and "two arcs of a closed curve meet only if one contains an endpoint of the other") |
| 38 | the exterior analogue of 37 | no proof printed (expected: 29, 27, via 37's argument) |
| 39 | every point not on `J` is joined to `O ∈ J` by an arc meeting `J` only in `O` | 20, 21, 25 ("cf. proof of Theorem 25"), 37; Theorem 36 for the curves `Jₙ` shrinking to `O`; a limit arc |
| 40 | `A`, `B` on `J` are joined by arcs within and without `J` | no proof printed (expected: 39 twice) |
| 41 | two closed curves with intersecting interiors: a closed curve from their points enclosing both interiors | 27, 38 |
| 42, 43 | finitely many closed curves: an enclosing curve; curves `J₁`, `J₂` through `O` | no proofs printed (expected: induction on 41) |

What is available for it:

* **Interiors.** `IsInteriorOf` with `existsUnique_interior`, and the bridge lemmas of `Sec6A.lean`
  (`isInteriorOf_iff`, `isSCC_iff_tscc`, `isArc_iff_tarc`, `bdry_eq_frontier`,
  `ext_eq_compl_closure`, `locallyConnectedSpace`, `arcConn`).
* **Theta-curves.** Theorems 24–27, 29, 30 both as Moore statements and in topological form
  (`Gen.th24_sub`, `Gen.th24_ext`, `Gen.th24_disj`, `Gen.th25`, `Gen.th26`, `Gen.th27`,
  `Gen.th27_dich`, `Gen.th29`, `Gen.th30`, `Gen.tscc_of_open_disjoint` — a theta-curve's two new
  closed curves are closed curves). Theorem 41's "the curve `PBCA` contains `I₂`" is
  `Gen.th27_dich`.
* **Arcs.** `Gen.TArc` API (`first_point`, `exists_sub`, `union`, `join`, `split`), order on an arc
  (`Gen.order_of_arc_sub`, `Gen.TArc.mem_of_isPreconnected`), `Gen.exists_access`,
  `Gen.exists_cross` (Moore's repeated "cf. proof of Theorem 25", which Theorem 39 also cites).
* **Limit arcs.** `Gen.tarc_of_seq` / `Gen.exists_tarc_of_seq`: Theorem 39's final step ("the
  point-set `O + P₁P_{n₂} + P_{n₂}P_{n₃} + ⋯` is an arc") is exactly this.
* **Accessibility.** `accessible` (Theorem 32's general form) and `reach_end`. Theorem 39 is an
  accessibility statement for a closed curve; near `O` the curve is an arc, so `accessible` applied
  to a sub-arc of `J` ending at `O` and to the interior (or exterior) of `J` may replace Moore's
  shrinking curves `Jₙ` and Theorem 37 altogether. This is a suggestion, not checked.
* **Theorems 33, 34** for any region (`fa_theorem33`, `fa_theorem34_region`), and `th31_pocket`.

Axioms: §7's heading omits Axioms 6 and 7, but §6 as formalized uses them (Theorem 21 uses
Axiom 7; Theorems 28, 31–34 use Axiom 6). Batch 139 should expect Axioms 1–8 throughout, unless it
re-proves Theorems 21 and 28 from 1–5, 8 (not attempted here).
