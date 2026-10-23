# Open items

The declarations of the main build (`HPC.lean`) whose proof is `sorry` (none since batch 132). Each one is marked
`-- OPEN (see OPEN.md)` in its file, and each appears in the group *Open targets* of
`Axioms.lean` / `axioms.txt`. They are the only places where `sorryAx` occurs in the main audit:
no theorem of the main build depends on them, so the group *Consequences of open targets* is empty.
The items were renumbered in batch 116 and again in batch 123 (former item 1, `theorem3_end`, closed);
the items closed earlier are listed at the end. Former item 2 (an open statement recorded as a
`Prop`, Theorem 4 as printed with `m ≥ 4`) was closed in batch 125.

---

## Open items not scheduled

* **Bing 1948, Theorem 9 as printed (the two-link form).** Bing (p. 737) requires "each link of F
  [to be] a subset of the sum of two adjacent links of E". `HPC.Fold.theorem9` (`Fold/Theorem7.lean`)
  proves the three-link form (every block of `F` in three consecutive links of the Lean statement's
  `D`, which is Bing's `E`); the two-link form is not formalized. Not scheduled (recorded in batch
  204).

---

## Batch 202: Part G, V (Bing–Jones §7, a plane circle of pseudo-arcs), items left open

**Proved in batch 202** (`HPC/BJ59/CircDescr.lean`, `CircFibre.lean`, `CircMap.lean`, `Sweep.lean`,
`SweepPattern.lean`, `CircJoints.lean`, `CircCover.lean`, `CircDescent.lean`, `CircStd.lean`,
`CircStep.lean`, `CircPlane.lean`, `Sweep3.lean`, `NonVac202.lean`, `NonVac202b.lean`, `NonVac202c.lean`,
collected by `BJ59E.lean`; report `doc/batches/REPORT-batch202.md`): every declaration of the
skeleton of commission 202, with the skeleton's statements: `CircDescr.isCompact_M`,
`CircDescr.inter_M_nonempty`, `CircDescr.fib_meets`, `CircDescr.isCircleOfPA`,
`exists_sweepPattern`, `stdCircLink_meet_iff`, `circ_step`, `exists_circDescr_plane`,
`bjPlaneExample`, `ho16_classification₄`, `ho16_classification_plane₄`, `dp22_theorem61'`,
`dp22_theorem61_iff'`, `hoCircleLike'`. Nothing is commented out and nothing uses `sorry`.

**The named input `HPC.BJ59.BJPlaneExample` is closed** by `bjPlaneExample` in
`HPC/BJ59/BJ59E.lean`. With `bjThm10` (batch 201), the classification of homogeneous plane
continua with Bing–Jones's third class holds with no named hypothesis.

**The non-vacuity omission of batch 201 is supplied**: non-degenerate witnesses for `BJThm10`,
`BJStep`, `bj_theorem8_cor_sub` and `bj_theorem5_window` (with `exists_window_set` used inside the
last) from a half of the plane example (`HPC/BJ59/NonVac202b.lean`).

**Still open / not done:**
* `HPC.BJ59.isAtriodic_of_atomic` (batch 199, optional; not attempted).
* (Not open; recorded for the shape.) The sweep lemma is used with at most two events
  (`sweep_lemma`, `HPC/BJ59/Sweep.lean`), which is all the sweep pattern needs; the commission's
  bound, at most three events, is proved as `sweep_lemma3` (`HPC/BJ59/Sweep3.lean`), tested on a
  window with exactly three events (`nonvac_sweep_three_events`), and shown sharp by a walk with
  four events that is not crooked (`nonvac_sweep_four_events`, `HPC/BJ59/NonVac202c.lean`).
* The certificate of commission §4.4 (with one sweep per period, survival fails) was not
  formalized (the commission asks for it only "if it is cheap").
* The certificate of commission §7 item 3 (two chains each crooked in a pair of consecutive
  columns whose concatenation is not crooked) was not given.

---

## Batch 201: Part G, IV (Bing–Jones §6, Theorem 10), items left open

**Proved in batch 201** (`HPC/BJ59/Thm10Defs.lean`, `Thm10Lib.lean`, `Thm10Runs.lean`,
`Thm10Pattern.lean`, `Thm10Window.lean`, `Thm10Sub.lean`, `Thm10Glue.lean`, `Thm10Pieces.lean`,
`Thm10Induct.lean`, `Thm10Step.lean`, `NonVac201.lean`, `NonVac201b.lean`, collected by
`BJ59D.lean`; report `doc/batches/REPORT-batch201.md`): every declaration of the skeleton of
commission 201, with the skeleton's statements except `exists_pattern` (second clause
strengthened; the skeleton's form is `exists_pattern_skeleton`): `exists_point_only_of_minimal`,
`adjacent_of_properCover`, `isFibreFine_of_isEpsChain`, `exists_pattern`, `bj_theorem8_cor_sub`,
`bj_theorem5_window`, `exists_window_set`, `bj_step`, `bjThm10_of_step`, `bjThm10`,
`ho16_classification_atomic'`, `isHomogeneous_of_isCircleOfPA'`, `homeomorph_of_isCircleOfPA'`,
`ho16_classification₃`, `ho16_classification_plane₃`, `nonvac_conditions`. Nothing is commented out
and nothing uses `sorry`.

**The named input `HPC.BJ59.BJThm10` (Bing–Jones Theorem 10) is closed** by `bjThm10` in
`HPC/BJ59/BJ59D.lean`.

**Still open:** the named input `HPC.BJ59.BJPlaneExample` (a circle of pseudo-arcs in the plane);
`HPC.BJ59.isAtriodic_of_atomic` (batch 199, optional; not attempted).

**Non-vacuity not supplied:** an unconditional witness for the hypotheses of `bj_theorem8_cor_sub`,
`bj_theorem5_window`, `exists_window_set`, `BJStep` and `BJThm10` (a continuous snake-like arc of
pseudo-arcs). None is known without `BJPlaneExample`; a conditional witness was not attempted
(commission 201 §7 does not require it).

---

## Batch 200: Part G, III (Bing–Jones §§4–6: the homeomorphism of pp. 188–189, Theorems 8 and 9), items left open

**Proved in batch 200** (`HPC/BJ59/Zigzag.lean`, `Private.lean`, `Step1b.lean`, `Thm8Lib.lean`,
`Thm8.lean`, `Thm8Cor.lean`, `Thm9Class.lean`, `Thm9D.lean`, `Thm9E.lean`, `Thm9Base.lean`,
`Thm9.lean`, `DP61.lean`, `NonVac200.lean`, `NonVac200b.lean`, collected by `BJ59C.lean`; report
`doc/batches/REPORT-batch200.md`): every declaration of the skeleton of commission 200, with the
skeleton's statements: `zigzag_homeomorph`, `zigzag_fibre`, `exists_privatePoint_interior`,
`exists_privatePoint_shrink`, `bj_step1b`, `bj_theorem8`, `bj_theorem8_cor`, `bj9_base`,
`bj_theorem9`, `dp22_theorem61_iff` (from `BJThm10`, `BJPlaneExample`), `bj_theorem7_proof_n3`,
`nonvac_zigzag`. Nothing is commented out and nothing uses `sorry`.

**Batch 199's open item `HPC.BJ59.bj_theorem9` is closed** by `bj_theorem9` in
`HPC/BJ59/Thm9.lean` (same statement). The commented-out copy in `HPC/BJ59/BJ59B.lean` is left as
it was (that file is not edited).

**Still open:** `HPC.BJ59.isAtriodic_of_atomic` (batch 199, optional; not attempted); the named
inputs `HPC.BJ59.BJThm10` (Bing–Jones Theorem 10) and `HPC.BJ59.BJPlaneExample`. For Theorem 10,
Steps 2 and 3 (pp. 182–188), the induction and the assembly remain (see the report, §9); all the
tools named by commission 200 §1 are now available.

**Non-vacuity not supplied:** an unconditional witness for the hypotheses of `bj_theorem8` and
`bj_theorem8_cor` (a continuous snake-like arc of pseudo-arcs with a chain of at least three links
each meeting every fibre). None is known without `BJPlaneExample`; not attempted (commission 200 §8
does not require it).

---

## Batch 199: Part G, II (Domokos–Prajs Theorem 6.1; Bing–Jones Theorems 7 and 9), items left open

**Proved in batch 199** (`HPC/BJ59/Atomic.lean`, `CircleLike.lean`, `AtomicCircle.lean`,
`BJChains.lean`, `Thm7Fold.lean`, `Thm7Core.lean`, `Thm7.lean`, `Thm7Ends.lean`, `Thm7Ends2.lean`,
`BJ59B.lean`, `NonVac199.lean`; report `doc/batches/REPORT-batch199.md`): every theorem of the
skeleton of commission 199 except the two below, including `isSnakeLike_of_atomic'` (Bing's 1951
argument), `dp22_theorem61` (from `BJThm10`), `circle_or_atomic_of_decomposable`,
`ho16_classification_atomic`, `bj_theorem7`, `bj_theorem7_ends` (`n ≥ 3`) and the certificate
`bj_theorem7_ends_printed_false`. `HOCircleLike` is now a theorem (`hoCircleLike`, from `BJThm10`
and `BJPlaneExample`).

**Commented out, with `sorry`, in `HPC/BJ59/BJ59B.lean`:**
* `HPC.BJ59.bj_theorem9` (Bing–Jones Theorem 9, p. 179; the stretch item of commission 199 §6).
  Obstruction: not attempted. The proof (pp. 179–181) is a back-and-forth construction of a
  homeomorphism from two sequences of chains with refining chain maps; in the library it would need
  a two-sided generalization of `Description.exists_homeomorph` together with the bridge from
  Bing–Jones's chains (`IsBJChain`) to the library's descriptions.
* `HPC.BJ59.isAtriodic_of_atomic` (Domokos–Prajs p. 14, "one can easily show that X is atriodic";
  optional, commission 199 §4/§7). Obstruction: not attempted; needs the facts on subcontinua of
  the circle (three arcs pairwise meeting in one arc or point) and the case split of `LEDGER.md`
  DP.1. Not used by any theorem.

**Open inputs, recorded as named `Prop`s:** `HPC.BJ59.BJThm10` (Bing–Jones Theorem 10) and
`HPC.BJ59.BJPlaneExample` (a plane circle of pseudo-arcs), as in batch 198. `HOCircleLike` is no
longer an input. `ho16_classification_atomic` needs only `BJThm10`.

**Optional items of commission 199 §7, done in a continuation of batch 199:** the general
certificate for Theorem 5 (BJ.5) as a lemma (`bj_theorem5_printed_false_general`,
`HPC/BJ59/Thm5Cert.lean`), and `IsBJChain D ↔ IsTaut D`, in every metric space
(`isBJChain_iff_isTaut`, `HPC/BJ59/Taut.lean`). `isAtriodic_of_atomic` remains open, as above.

---

## Batch 198: Part G, I (the circle of pseudo-arcs, Bing–Jones 1959, top down), items left open

**Proved in batch 198** (`HPC/BJ59/Defs.lean`, `Order.lean`, `ChainOps.lean`, `Arc.lean`,
`Thm3Assembly.lean`, `Thm3.lean`, `Thm5.lean`, `Thm56.lean`, `Transfer.lean`, `Halves.lean`,
`Glue.lean`, `Homog.lean`, `CircleFacts.lean`, `Decomp.lean`, `BJ59A.lean`, `NonVac198.lean`; report
`doc/batches/REPORT-batch198.md`): every theorem of the skeleton, including the stretch
`bj_theorem5` (Theorem 5 repaired) and the certificate `bj_theorem5_printed_false`. No declaration
is commented out and none uses `sorry`. `isPseudoArc_Lset` is unconditional; the classification
theorems are proved from the named inputs below.

**Open inputs, recorded as named `Prop`s** (not `sorry`s; `HPC/BJ59/Defs.lean`):
* `HPC.BJ59.BJThm10`: Bing–Jones Theorem 10 (pp. 181–182), fibre-preserving form. Hypothesis of
  `isHomogeneous_of_isCircleOfPA`, `homeomorph_of_isCircleOfPA`, `ho16_classification`,
  `ho16_classification_plane`. Obstruction: not attempted (commission 198 asks only for §§3–4 of
  Bing–Jones bottom up); needs Theorems 7–9 and the construction of pp. 182–189, and a bridge to
  Bing–Jones's chains (nonadjacent links with disjoint closures).
* `HPC.BJ59.HOCircleLike`: a decomposable homogeneous plane continuum is circle-like (not in
  Bing–Jones). Hypothesis of `circle_or_circleOfPA_of_decomposable`, `ho16_classification`,
  `ho16_classification_plane`. Obstruction: not attempted; no source in hand (the expected route is
  through `jones55_c` and Lewis 1985).
* `HPC.BJ59.BJPlaneExample`: a plane circle of pseudo-arcs (Bing–Jones §7, a sketch). Hypothesis of
  `ho16_classification_plane`. Obstruction: not attempted; §7 asserts the chains (1)–(9) without
  construction (`LEDGER.md` BJ.15).

**Optional items not done:** `¬ IsSnakeLike univ` for a circle of pseudo-arcs (commission §2), and
the general certificate for Theorem 5 as a lemma (commission §6; the construction is given in prose
in `LEDGER.md` BJ.5).

---

## Batch 197: H–O Theorem 1, V (Theorem 15 by ladders; the end of Part F), items left open

**Proved in batch 197** (`HPC/HO16/LadderDefs.lean`, `LadderParam.lean`, `LadderPiece.lean`,
`LadderStair.lean`, `LadderStair2.lean`, `LadderSubdiv.lean`, `LadderSign.lean`, `LadderSep.lean`,
`LadderExists.lean`, `HO16E.lean`, `NonVac197.lean`; report `doc/batches/REPORT-batch197.md`):
every item of commission 197 §2–§6, including the stretch of §5. No declaration is commented out
and none uses `sorry`. **Nothing new is open.**

**Closed:** the open input `HPC.HO16.HOThm15` of batch 196 (below) is now proved
(`ho16_theorem15 : HOThm15`, `HPC/HO16/HO16E.lean`), and with it `ho16_theorem20 : HOThm20`. So
`HPC.HO16.HOThm20`, recorded as an open input since batch 193, is closed as well, and
`ho16_indec_homogeneous_pseudoArc` (every indecomposable non-degenerate homogeneous plane continuum
is a pseudo-arc, H–O p. 180) holds with no named hypothesis, on the three standard axioms. The
named `Prop`s `HOThm15` and `HOThm20` remain in the library as statements; the `_of_thm15`
theorems are unchanged.

**What remains of the classification** (not commissioned in this batch; see the report, §8): the
decomposable case (H–O Part G: a decomposable homogeneous plane continuum is a circle of
pseudo-arcs), the converse (the circle of pseudo-arcs is homogeneous, Bing–Jones 1959), and the
final statement with all three cases.

---

## Batch 196: H–O Theorem 1, IV (Proposition 19; Theorem 20 from Theorem 15), items left open

**Proved in batch 196** (`HPC/HO16/P19Defs.lean`, `OrdFold.lean`, `P19Lib.lean`, `P19Ctx.lean`,
`Prop19A.lean`–`Prop19D.lean`, `Prop19.lean`, `Prop19Conn.lean`, `P208.lean`, `Thm20.lean`,
`HO16D.lean`, `NonVac196.lean`; report `doc/batches/REPORT-batch196.md`): every item of commission
196 §2–§5, including the stretch items of §5 (`ho16_lift_stairwell`, `ho16_theorem20_of_thm15`,
`homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`). Proposition 19 is proved in full
(`ho16_prop19_full`, `ho16_prop19`, and `hoProp19_holds : HOProp19`). No declaration is commented
out and none uses `sorry`.

**Open input, recorded as a named `Prop`** (not a `sorry`):
* `HPC.HO16.HOThm15` (`HPC/HO16/P19Defs.lean`): H–O Theorem 15 (p. 194), stairwell structures of
  odd height near a separator, for connected PL graphs. It is the only hypothesis of
  `ho16_theorem20_of_thm15 : HOThm15 → HOThm20` and of
  `homeomorph_pseudoArc_of_indec_homogeneous_of_thm15`, and so the only open input of the
  `_of_thm15` route to the classification. Obstruction: not attempted in this batch (scheduled for
  a later batch; see the report, §7, for the plan). **Closed in batch 197** (`ho16_theorem15`). It is stated for connected `G`; without
  connectedness (`G = ∅`) it would be false.

`HPC.HO16.HOThm20` remains a hypothesis of `homeomorph_pseudoArc_of_indec_homogeneous` (batch 193);
it now follows from `HOThm15`.

---

## Batch 195: H–O Theorem 1, III (sides; straight sets, stairwells; Proposition 17, Lemma 18), items left open

**Proved in batch 195** (`HPC/HO16/StairDefs.lean`, `PLLib2.lean`, `SidesLib.lean`, `Sides.lean`,
`StairLib.lean`, `Stairwell.lean`, `Lemma18.lean`, `StairExample.lean`, `HO16C.lean`; report
`doc/batches/REPORT-batch195.md`): every item of commission 195 §2–§9, including the stretch item
`ho16_prop19_fold` (§8). No declaration is commented out and none uses `sorry`. Nothing new is open.

**Open input, unchanged:** `HPC.HO16.HOThm20` (see batch 193 below). Of its proof (H–O §§4–6),
Definitions 9, 12, 13, 16, Propositions 10, 11, 17, Lemma 18, Claim 14.1 and the first step of
Proposition 19 (the fold and (19.1)–(19.3)) are now in place, on top of simple folds, Lemma 6,
Proposition 7 and Theorem 8 (batch 194). Theorem 15, the rest of Proposition 19 (pp. 203–209) and
Theorem 20 remain (scheduled for later batches).

---

## Batch 194: H–O Theorem 1, II (PL graphs; simple folds; Lemma 6, Theorem 8, Proposition 7), items left open

**Proved in batch 194** (`HPC/HO16/FoldDefs.lean`, `Subdiv.lean`, `PLLib.lean`, `Lemma6.lean`,
`FoldExists.lean`, `Thm8Fold.lean`, `Prop7.lean`, `FoldExample.lean`, `HO16B.lean`; report
`doc/batches/REPORT-batch194.md`): every item of commission 194 §2–§8. No declaration is commented
out and none uses `sorry`. Nothing new is open.

**Open input, unchanged:** `HPC.HO16.HOThm20` (see batch 193 below). Of its proof (H–O §4–§5),
simple folds (Definition 5, the construction of pp. 185–186), Lemma 6, Proposition 7 and Theorem 8,
(1) ⇒ (2), for folds are now in place; Definitions 9, 12, 13, 16, Propositions 10, 11, 17, 19,
Lemma 18, Theorem 15 and Theorem 20 remain (scheduled for later batches).

---

## Batch 193: H–O Theorem 1, I (Theorems 4 and 8; plane graphs; `HOThm20`), items left open

**Proved in batch 193** (`HPC/HO16/Defs.lean`, `KM77.lean`, `Thm8.lean`, `Thm4.lean`, `Grid.lean`,
`Plane.lean`, `HO16A.lean`; report `doc/batches/REPORT-batch193.md`): every item of commission 193
§2–§7. No declaration is commented out and none uses `sorry`.

**Open input, recorded as a named `Prop`** (not a `sorry`):
* `HPC.HO16.HOThm20` (`HPC/HO16/Defs.lean`): H–O Theorem 20, "only if" direction, for PL graphs in
  a real normed space. It is a hypothesis of `ho16_theorem1_plane`,
  `isPseudoArc_of_indec_homogeneous` and `homeomorph_pseudoArc_of_indec_homogeneous`, and the only
  open input on the dependency map of the last. Obstruction: not attempted in this batch; the
  commission schedules it for later batches (simple folds, Theorem 8 for folds, Theorem 15,
  Theorem 20; commission 193 §8). It is not refuted, and it is not equivalent to the conclusions it
  is used for (it says nothing about homogeneity or span).

---

## Batch 192: Theorem C II (the strip theorem; `OTThm32`; Theorem C), items left open

**Closed in batch 192** (`HPC/Span/OT82Parity.lean`, `OT82Zero.lean`, `OT82Strip.lean`,
`OT82Order.lean`, `OT82B.lean`; report `doc/batches/REPORT-batch192.md`): every item of commission
192 §3–§7 is proved, including both items left open in batch 191:
* `OTThm32` is proved (`HPC.Span.ot82_theorem32 : OTThm32`), so `TheoremC` holds without
  hypotheses (`HPC.Span.theoremC : TheoremC`);
* `crossing_traces_separated` (commission 191 §7) is proved (`HPC/Span/OT82Order.lean`).

Nothing is left open in batch 192. No declaration of the main build uses `sorry`.

---

## Batch 191: Theorem C I (span; Cook 1967; O–T 1982 Theorem 3.6 and Corollary 3.5), items left open

**Closed in batch 191** (`HPC/Span/Defs.lean`, `Cook.lean`, `Thm36.lean`, `Reembed.lean`,
`Crossing.lean`, `OT82A.lean`; report `doc/batches/REPORT-batch191.md`): every item of commission
191 §2–§6 is proved, ending with `theoremC_of_thm32 : OTThm32 → TheoremC`. No declaration of the
main build uses `sorry`.

Still open after batch 191 (**both closed in batch 192**, see above):
1. **`OTThm32`** (`HPC/Span/OT82A.lean`, a named `Prop`; O–T Theorem 3.2 in strip form, with the
   images inside pairwise disjoint continua crossing the strip `[0, 1] × ℝ`). It is the only open
   input of `TheoremC`. Obstruction: it needs O–T §2 (Lemmas 2.1–2.4, Remark 2.5, Theorem 2.7) and
   the three-images argument of Theorem 3.1, none of which is formalized; batch 192 is commissioned
   for it. See `doc/notes/ot82.md` for what is needed.
2. **`crossing_traces_separated`** (commission 191 §7; commented out at the end of
   `HPC/Span/OT82A.lean`, statement as in the skeleton): two disjoint continua crossing the strip
   `[a, b] × ℝ` have non-interleaved traces on the left line. Not used in batch 191 (commission §8
   allows leaving it for batch 192). Obstruction: the two Jordan-curve lemmas of §7 (*crosscut*
   and *pocket*, for an arc in the strip meeting the side lines only at its ends) are not in the
   repository in strip form; the nearest results (`rect_domain_crosscut`,
   `rect_domain_crosscut_arc`, the `VFrame` order of `HPC/Hagopian/H76Order.lean`) need a domain
   with a prescribed frontier or abstract pieces, and were not adapted in this batch.

---

## Batch 190: Jones 1975 II (the planar core; `NoArcIndecHomPlane`; Theorem 1 of 1976), items left open

**Closed in batch 190** (`HPC/Jones/Jones75Pass.lean`, `Jones75Shadow.lean`, `Jones75Region.lean`,
`Jones75Trap.lean`, `Jones75B.lean`; report `doc/batches/REPORT-batch190.md`). Every item of
commission 190 §2–§6 is proved:
* **§2** passes and (P1)–(P4) (`IsPass`, `PassMon`, `IsPass.disjoint`, `IsPass.finite`,
  `exists_first_pass`, `isPass_base`, `IsPass.above_or_below`).
* **§3** the shadow lemma, the flow box, scale 2, late thin passes (`shadow_pass`, `flow_box`,
  `scale_two`, `exists_late_thin_pass`), in the middle band.
* **§4, §7** N1–N4 and (R1)–(R3) (`thinPass_arc`, `tarc_lowest`, `two_sides`,
  `IsPass.lc_left_mem_closure`, `region_pass`, `region_thin_above`, `region_cross`).
* **§5** Lemma A and the trap (`region_lemmaA`, `trap_jordan`, `trap_pass`).
* **§6** the contradiction (`jones75_contra`), **`jones75_noArc : NoArcIndecHomPlane`** (the batch-188
  and batch-189 open item), **`hagopian76_theorem1 : Hagopian76Thm1`**, and the unconditional
  `bing60_plane_uncond`, `hagopian76_theorem2_uncond`, `hagopian75_corollary_uncond`,
  `hagopian75_theorem2_uncond`, `hagopian75_theorem1_of_noArc_uncond`.

Still open after batch 190 (no `sorry` in any declaration): **nothing on the route to
`Hagopian76Thm1`**; its dependency map has no open input. The commented-out copies of the open
statement in `Hagopian76P.lean`–`Hagopian76Y.lean` and `Hagopian76AB.lean` are replaced by one-line
pointers.
* **Not formalized, no longer needed:** the remaining items of the 1976 route (Hagopian's own proof
  of Theorem 1: `hagopian76_property4_step`, `hagopian76_T15_T17` and the other commented-out items
  of `Hagopian76P.lean`–`Hagopian76AB.lean`), Lemmas 8 and 10 of 1984, Jones's (e) and (f) as
  printed. They stay recorded in the sections below for the ledger; none is an input of a main-line
  theorem.

---

## Batch 189: Jones 1975 I (arcs and lines; no small reversal; recurrence; (L)), items left open

**Closed in batch 189** (`HPC/Jones/Jones75Arcs.lean`, `Jones75Line.lean`, `Jones75Rev.lean`,
`Jones75L.lean`, `Jones75A.lean`; report `doc/batches/REPORT-batch189.md`). Every item of commission
189 §2–§5 is proved, for a compact metric `Y` with `JonesSetting Y`:
* **§2** (c) (`JonesSetting.union_arc`, `JonesSetting.nested`), `JonesSetting.exists_arc_through`,
  lines (`arcComp`, `IsLine`, `JonesSetting.exists_line`), `JonesSetting.line_arc`,
  `JonesSetting.homeo_on_line`.
* **§3** (R0), (R), (O) (`JonesSetting.no_reversal_arc`, `JonesSetting.exists_no_reversal`,
  `JonesSetting.orientation`).
* **§4** recurrence (`omegaLim`, `IsArcSaturated`, `JonesSetting.omegaLim_saturated`,
  `JonesSetting.line_recurrent`, `JonesSetting.jones75_d`).
* **§5** (L) (`JonesSetting.no_backtrack`, `no_backtrack_in_collar`).

Still open after batch 189 (no `sorry` in any declaration):
* **`NoArcIndecHomPlane`** (`jones75_noArc`, the planar core of Jones's Theorem; **closed in batch
  190**): the last open input of `Hagopian76Thm1` on the 1984 route. *Obstruction:* not attempted in this batch (the
  commission asks for a reconnaissance only). The planar argument needs, besides what the repository
  has (`jordan_curve_theorem`, `jordan_side`, the θ-curve lemma `theta_no_common_side`,
  `janiszewski_compact`, `exists_collar`, Schoenflies, the collar cross-cut `rect_domain_crosscut`),
  a general cross-cut lemma for a box in collar coordinates crossed by finitely many disjoint passes
  (the region between two passes, and its left and right parts). Hand proof (Poincaré–Bendixson
  route) and skeleton proposal in the report §6.
* **Not formalized (not needed on this route):** Jones's (e) and (f) as printed (the proof of (f) is
  defective, ledger J75.1), and the solenoid example (hand argument only).

---

## Batch 188: Hagopian 1984 V (`𝔇`; claims (5)–(6); `hagopian84_decomp`), items left open

**Closed in batch 188** (`HPC/Hagopian/Hagopian84D.lean`; report `doc/batches/REPORT-batch188.md`):
* **The transfer lemma** (`omega_layer_of_mem_mid`, `omega_mem_delta_of_mem_mid`).
* **The relation `𝔇`** (`CoverData84`, `exists_coverData84`, `CoverData84.members`,
  `CoverData84.members_disjoint`, `CoverData84.setoid`, `CoverData84.cls_eq`).
* **Claims (5)–(6)**: (5) for `i = 0` in full, for `i ≥ 1` for the members inside `⋃𝒫(Zᵢ)′`
  (`CoverData84.omega_subset_members`, `CoverData84.omega_mem_members`); (6) (`CoverData84.invariant`).
* **The fields of `IsJonesDecomp84`** (`CoverData84.isJonesDecomp`) and **`hagopian84_decomp`**;
  **`hagopian76_theorem1_jones`** (Theorem 1 of 1976 from `NoArcIndecHomPlane` alone).
* **The printed closedness of `⋃𝔅`** (batch 187's first open item): *printed reason unargued;
  statement proved* (`sUnion_cover84_eq_univ`: for any choice as in `exists_finite_cover84`,
  `⋃𝔅 = M`). Ledger H84.29 reclassified.

Still open after batch 188 (no `sorry` in any declaration):
* **`NoArcIndecHomPlane`** (the arc step, Jones 1975): the last open input of `Hagopian76Thm1` on the
  1984 route. Skeleton proposal in the report §10.
* **Not formalized, not needed:** the printed (5) for members of `Ω(𝒫(Zᵢ))` outside `⋃𝒫(Zᵢ)′` (an
  argument is recorded in the report §4.2); the lower semicontinuity of `𝔇` (ledger H84.34); the
  "first note" of p. 344 (ledger H84.35: unargued, not used).
* **Unchanged:** the 1976 route items, and Lemmas 8 and 10 (not needed with `N = M`).

---

## Batch 187: Hagopian 1984 IV (Lemma 13; Lemma 16′; the bridge `J(Z)`; `𝒫(Z)`; the cover), items left open

**Closed in batch 187** (`HPC/Hagopian/Hagopian84C.lean` and `H84Strand.lean`, `H84Bridge.lean`,
`H84Chain13.lean`, `H84Runs13.lean`, `H84Regular13.lean`, `H84Lemma13.lean`, `H84Cover.lean`; report
`doc/batches/REPORT-batch187.md`):
* **Lemma 13** (`hagopian84_lemma13`) and the chain of its proof: `chainLinks84_chain`,
  `chainLinks84_runsStraight`, `chainLinks84_regular` (batch-186 shapes). Batch 186's items
  "Lemma 13 (with the chain of its proof)" are closed.
* **Lemma 16′** (`strand_layer_of_extension`), with the identification (`strand_layer_mem_delta`)
  and the impossibility of the degenerate alternative (`not_strand_subset_extension_layer`).
* **Lemma 16 as printed** (`hagopian84_lemma16`, normality added, the unused hypothesis
  `Cl K ⊆ F` dropped), from Lemma 16′. Batch 186's item "Lemma 16 and its weaker form" is closed.
* **§4.2** (`omega_not_delta_side`) and **the bridge** (`exists_bridge84`, the skeleton statement).
* **`𝒫(Z)`** (`exists_chainZ84`, with `Z ∈ Δ(𝒫(Z))`, `mem_delta_of_bridge_chain`).
* **The finite cover** (`hagopian84_cover`, `exists_finite_cover84`).

Still open after batch 187 (no `sorry` in any declaration):
* **The printed closedness of `⋃𝔅`** (commission 187 §5.2). *Obstruction:* "it follows that `⋃𝔅`
  is a closed open subset of `M`" is unargued: freeness of `𝒫` and of each `𝒫(Z)`, with (3), control
  `Bd ⋃𝒫(Z)` for each `Z` separately, and for a limit of points of `⋃Δ(𝒫(Zₙ))` with pairwise distinct
  `Zₙ` nothing places it in `⋃𝔅`. Not needed: the finite subcover, which is what the proof uses
  afterwards, is proved directly (`hagopian84_cover`: `Cl ⋃Δ(𝒫) ∖ ⋃Δ(𝒫)` is compact and covered by
  the open sets `⋃Δ(𝒫(Z))`). *Batch 188:* printed reason unargued; statement proved
  (`sUnion_cover84_eq_univ`).
* **The relation `𝔇`, claims (5)–(6), the fields of `IsJonesDecomp84` and `hagopian84_decomp`**: not
  started (skeleton proposal in the report §8). *Closed in batch 188.*
* **Unchanged:** the 1976 route items, Lemmas 8 and 10 (not needed with `N = M`), and
  `NoArcIndecHomPlane`. The commented-out batch-184 copy of `hagopian84_lemma13` in
  `Hagopian84A.lean` is left in place (that file is not on the commission's list of editable files).

---

## Batch 186: Hagopian 1984 III (the quotient package; Lemmas 12–16), items left open

**Closed in batch 186** (`HPC/Hagopian/Hagopian84B.lean` and `H84Fold.lean`, `H84Delta.lean`,
`H84Lemma12.lean`, `H84Lemma1415.lean`; report `doc/batches/REPORT-batch186.md`):
* **The quotient package** (`hagopian84Decomp_of_package`): `Hagopian84Decomp` from Jones
  decompositions (`IsJonesDecomp84`); homogeneity by the orbit argument (`exists_comp_small_homeo`).
* **The fold combinatorics** (`exists_fold`).
* **Lemma 12** (`hagopian84_lemma12`, with the added components clause).
* **The note on p. 341 and positivity** (`delta5_partition`, `delta5_dist_pos`).
* **Lemma 14** (`hagopian84_lemma14`) and **Lemma 15** with a smaller `ε` (`hagopian84_lemma15`).
* **The interval of layers for the arc** (`exists_interval_in_delta`).

Still open after batch 186 (statements commented out in `Hagopian84B.lean`; no `sorry` in any
declaration):
* **`chainLinks84_runsStraight`** (Lemma 13, (1)–(4) and the geometry of the fold; shape chosen and
  written in the comment). *Obstruction:* (1)–(4) are not formalized. The positions of `r` and `s`
  in (3) (commission 186 §3.1.3) need the `½ρ` bounds converted into parameter bounds through the
  uniform continuity of `t ↦ k⁻¹(t)` (upper semicontinuity of the layers); (4) needs Lemma 1 with
  Effros around a boundary point; the two kinds D and U of fold (commission 186 §3.1.4(b)) are not
  formalized. The combinatorics (`exists_fold`) are proved.
* **`chainLinks84_regular`** (Lemma 13, step 5; shape chosen). *Obstruction:*
  `chainLinks84_runsStraight`; the step itself (`Cl K ⊆ h[E]` by `subset_of_meets_avoids`, then
  Lemma 6) has no further gap.
* **Lemma 13** (`hagopian84_lemma13`). *Obstruction:* the two items above. Given them, the rest is
  assembled from proved pieces (Lemma 12 with its components clause).
* **Lemma 16** (`hagopian84_lemma16`) and its weaker form (no layer of `F` contains the closure of a
  component of `⋃𝒫′`). *Obstruction:* the printed step "Since `𝒫` is free, there exist a 3-linked
  subchain `𝔔` of `𝒫` and numbers `t`, `w` greater than `s` such that (1) …" is unargued and no
  argument was found: freeness controls `Bd ⋃𝒫`, while (1) is about how `F` leaves `⋃𝒫`. The
  weaker form meets the same step. Available: `s > 0`, `s ∉ S` (`lsc_of_minimalAdmissible`),
  uniqueness (`hagopian75_lemma3_unique`).
* **The construction of pp. 343–344** (`K(Z)`, `X(Z)`, `F(Z)`, `J(Z)`, `𝒫(Z)`, the cover `𝔅`, the
  disjointness of `𝔇`, claims (5), (6)) and the assembly `hagopian84_decomp` (a Jones decomposition
  for every `M`; then `hagopian84Decomp_of_package`). Not started (commission 186 §1: a later batch).
* **Unchanged:** the 1976 route items of batch 185 below (`crossing_component_run`,
  `case1_between_runs`, the four named `Prop`s of `hagopian76_theorem1_of_cases4`), Lemmas 8 and 10
  (not needed with `N = M`), and `NoArcIndecHomPlane` (reconnaissance of Jones 1975 in
  `doc/notes/jones75.md`).

---

## Batch 185: Hagopian 1976 XXX (Lemma 7 of 1984; saturation; the case split), items left open

**Closed in batch 185** (`HPC/Hagopian/Hagopian76AC.lean` and `H84TwoSided.lean`, `H84Lemma7.lean`,
`H84Rigid.lean`, `H76Sat185.lean`, `H76Split185.lean`; report `doc/batches/REPORT-batch185.md`):
* **The two-sided extension** (`hagopian84_two_sided`, open since batch 158).
* **Lemma 7 of 1984** (`hagopian84_lemma7`; the named `Prop` `Hagopian84Lemma7` holds,
  `hagopian84Lemma7_holds`). Batch 184's item "Lemma 7" below is closed.
* **Rigidity and runs** (`layers_agree`, `translate_run`, `translate_run_right`).
* **Saturation (2e)** for Hagopian's `F` (`innerComponentsCross_hagopian`, unconditional), through
  `half_in_O_false` and `noncrossing_half_in_O_steps45`. The hypothesis `hICC` of the 1976 route is
  discharged.
* **The case split for `i ≥ 3`** (`blockLayersMeetSides3`); the hypothesis `BlockLayersMeetSides3`
  of the 1976 route is discharged; `d⁻¹(x₃)` meets a closed side segment (`layer_x3_meets_side`).
* **Theorem 1 from four named `Prop`s** (`hagopian76_theorem1_of_cases4`).
* `Wset84 x ε = Wset M ε x` (`wset84_eq_wset`).

Still open after batch 185 (statements commented out at the end of `Hagopian76AC.lean`; no `sorry` in
any declaration):
* **§3.3, runs of `F` along a translate** (`crossing_component_run`). *Obstruction:* `Cl C ⊆ h[E]`
  (from `strand_lemma`, since `C` lies in the strand through a middle point) and `layers_agree` give
  a common segment, but (i) the degenerate alternative `h[E]` inside one layer of `F` is not
  excluded, (ii) `translate_run` allows the end layer `d⁻¹(0)` as well as `d⁻¹(1)`, and (iii) no shape
  was found that is provable this way and strong enough for §6.
* **§6, "between" with runs** (`case1_between_runs`). *Obstruction:* §3.3; then as report 183 §3.
* **The four named `Prop`s of `hagopian76_theorem1_of_cases4`**: `StepFrame`, `LastStepClaims`,
  `Case1ClaimsE24`, `Case2ClaimsE24` (obstructions as in batches 182–184 below; `hICC` and
  `BlockLayersMeetSides3` are no longer among them).
* **The 1984 route:** Lemmas 8, 10, 12–16, the arc in `M/𝔇`, `Hagopian84Decomp`, `NoArcIndecHomPlane`
  (batch 184 below; Lemma 7 is no longer an obstruction for Lemma 8 or for `K(Z)`, …, `𝒫(Z)`).

---

## Batch 184: Hagopian 1984 I (Theorem 1 of 1976 by Jones's plan), items left open

**Closed in batch 184** (`HPC/Hagopian/Hagopian84A.lean`, `HPC/Hagopian/H84Quot.lean`; report
`doc/batches/REPORT-batch184.md`; notes `doc/notes/hagopian84.md`):
* **§3, the assembly**: `hagopian76_theorem1_of_jones` (`Hagopian76Thm1` from the named `Prop`s
  `Hagopian84Decomp` and `NoArcIndecHomPlane`), with the plane quotient
  `exists_plane_quotient_of_monotone` (Moore 1925 Theorem 22 through `fibreSetoid`) and
  `indecomposable_of_monotone_image`.
* **§3, Hagopian 1975 Theorem 1 with paragraph 4 supplied**: `hagopian75_theorem1_of_noArc`
  (`hagopian75_theorem1_of_layer` without `hnd`, from `NoArcIndecHomPlane`).
* **§4, Lemma 1** (`hagopian84_lemma1`, `W(x, ε)` open, by Effros), **Lemma 6** (`hagopian84_lemma6`,
  without Thomas's Theorem 8), **Lemma 11 with `N = M`** (`hagopian84_lemma11`).

Still open after batch 184 (statements commented out at the end of `Hagopian84A.lean`; no `sorry` in
any declaration):
* **Lemma 7** (`hagopian84_lemma7`). *Obstruction:* Lemma 4 is used to put `E` and `F` inside type λ
  continua `H`, `I` missing both of their end sets, which needs the two-sided extension (open since
  batch 158); and three atriodicity steps are unargued (ledger H84.4).
* **Lemma 8** (`hagopian84_lemma8`). *Obstruction:* Lemma 7; the gluing of the two decompositions into
  one of `E ∪ F` onto "the union of two arcs"; "atriodic, no simple closed curve, hence an arc" is
  unargued (ledger H84.5).
* **Lemma 10** (`hagopian84_lemma10`), not needed with `N = M`. *Obstruction:* not attempted (the
  disjointness of `F`, `f[F]`, `g[F]` and the composant argument).
* **Lemma 12** (`hagopian84_lemma12`). *Obstruction:* Moore 1962 Theorem 44 is available
  (`exists_closed_split_of_no_connected`), but its hypothesis rests on the two unargued atriodicity
  steps, and that `𝒫` is free, normal and regular is not verified in the text (ledger H84.6).
* **Lemma 13** (`hagopian84_lemma13`). *Obstruction:* Lemma 12; in (3)–(5) the hypotheses of Lemma 3
  are not checked in the text; the regularity sentence "Since `M` is atriodic, it follows from (6) and
  Lemma 6 …" is unargued (ledger H84.7).
* **Lemmas 14, 15** (`hagopian84_lemma14`, `hagopian84_lemma15`). *Obstruction:* the hypotheses of
  Lemma 3 at "By Lemma 3, … `h[Z] = Zᵢ`" are not checked; `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′) > 0` needs
  `Cl ⋃Δ(𝒫) ⊂ ⋃𝒫′`, which is not argued (ledger H84.8).
* **Lemma 16** (`hagopian84_lemma16`). *Obstruction:* "Since `𝒫` is free, there exist a 3-linked
  subchain `𝔔` … such that (1) …" is unargued (ledger H84.9).
* **The arc in `M/𝔇`** (`hagopian84_quotient_arc`, no statement yet). *Obstruction:* needs the
  decomposition of Theorem 1; unargued in the paper (ledger H84.11); proposed argument in the report §5.
* **Theorem 1 with `N = M`** (`hagopian84_decomp : Hagopian84Decomp`). *Obstruction:* Lemmas 7, 8,
  13–16 and the steps of report §5 (the cover `𝔅`, disjointness, homogeneity of `M/𝔇`, the arc).
* **`hagopian76_theorem1_jones`** (`hagopian76_theorem1_of_jones hagopian84_decomp hA`), pending
  `hagopian84_decomp`; and **`NoArcIndecHomPlane`** (Bing 1960 or Jones 1975; reconnaissance in
  `doc/notes/hagopian84.md` §F, nothing formalized).

---

## Batch 183: Hagopian 1976 XXVIII (Theorem 1, Bing's reasons for Cases 1–2, E2.4, the orientation, saturation), items left open

**Closed in batch 183** (`HPC/Hagopian/Hagopian76AB.lean`, `H76Restrict.lean`, `H76E24.lean`; report
`doc/batches/REPORT-batch183.md`):
* **§2 steps 1–2, the pair `a`, `b` of E2.4** (Bing's arc `ab`): `Thm1Setup.cap_point_o`,
  `Thm1Setup.near_strand_cross_o`, `e24_pair_between`, `e24_pair_below`.
* **§2 step 3, `minimalAdmissible_restrict`** (with the layers kept; batch-182 proposal):
  `minimalAdmissible_restrict_of_lsc`, `minimalAdmissible_restrict`.
* **§2, `property2_violation`** (conditional on the three claims of steps 4–6) and E2.4 from the
  named `Prop` `E24Claims`: `e24_between_false`, `e24_below_far`, `E24Data.far`.
* **Theorem 1, strongest conditional form**: `hagopian76_theorem1_of_cases3` (fields `far` of Case 1
  and `claim_d` of Case 2 replaced by `E24Data`).

Still open after batch 183 (commented out at the end of `Hagopian76AB.lean`, or named `Prop`s; no
`sorry` in any declaration):
* **§2 steps 4–6** (`E24Claims`, `Thm1Setup.FarFrom`). *Obstruction:* the far layer needs the passage
  of `L` around the end of a strand; essentiality needs `H` to contain a piece of `Cl Cᵢ` essential to
  `h[R(E)]` (E2.1); "`H` does not come within `ε₂` of `π⁻¹(p₄)`" (T17) is unargued in Hagopian and
  in Bing; outside `D`, `L` may enter a pocket near `p₄` from the far side.
* **§3, "between"** (`case1_between_bing`). *Obstruction:* the two sides of the side subsegment `σ`
  between the strands' ends are separated by `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ σ`, but the outer component may reach
  `π⁻¹[D]` around an end of a strand if `F` has no points outside `D` there; Bing's strands end on the
  side line where the gap arc begins, which is not available for continua.
* **§4, Case 2 (a), (b), (e)** (`case2_bing_a`, `case2_curve`, `case2_gap_side`). *Obstruction:* (a) as
  §3; (b), (e): Bing's crossing-parity argument for the simple closed curve `J` has no analogue for the
  continuum `P`; the Janiszewski form separates the two sides of `Q`, not those of `S_I`.
* **§5, the two other orientations** (`property4_symm`). *Obstruction:* the proposal fails as stated:
  `f(yᵢ)` need not lie in `Mid`, the cap from `f(yᵢ)` uses `ε₃` fields stated on `Mid`, and the
  essentiality of the component of `f(yᵢ)` to `h₁[R(E)]` does not follow.
* **§6.1, E2.1 steps 1–3, 5** (`exists_first_crossing`). *Obstruction:* as batch 182.
* **§6.2, saturation** (`half_components_cross`, `chunk_points`; 2e, `innerComponentsCross_hagopian`).
  *Obstruction:* as batch 182.
* **§6.3, the split by `Γ`** (`gap_side_split`). Proposed split: `Γ` meets the left side segment between
  the strands, or the right one. *Obstruction:* exhaustiveness (`Γ` misses the bottom edge and `I₂`,
  and cannot join the strands inside the region between them without cutting `Cᵢ`) not formalized.
* **The named `Prop`s** `StepFrame`, `LastStepClaims`, `BlockLayersMeetSides3`, `Case1ClaimsE24`,
  `Case2ClaimsE24`, `E24Claims`. *Obstruction:* the items above.
* **`hagopian76_theorem1_final`.** *Obstruction:* by `hagopian76_theorem1_of_cases3`, exactly 2e and the
  five named `Prop`s of its hypothesis.

---

## Batch 182: Hagopian 1976 XXVII (Theorem 1, the last step, honest claims, saturation, E2.1 and E2.4), items left open

**Closed in batch 182** (`HPC/Hagopian/Hagopian76AA.lean`, `H76Last.lean`, `H76Orient.lean`,
`H76Sat182.lean`, `H76Tight.lean`; report `doc/batches/REPORT-batch182.md`):
* **§1.1, certificate**: `blockLayersMeetSides_false` (the batch-181 `BlockLayersMeetSides` is false
  for every set-up with blocks: `d⁻¹(x₂) = k⁻¹(1)` meets neither side segment).
* **§1.2, the last step**: `last_step_ending`, `not_property4_x3x4` (from the named `Prop`
  `LastStepClaims`).
* **§2.1, the mirror cap without extra hypothesis**: `cross_strand_near_above`.
* **§2.2, orientation**: `cross_strand_near_o`, `property4_step_unless_o`, `case1_ending_oriented`,
  `case2_ending_oriented`.
* **§2.3–§2.4, honest claims and the reduction**: `StepCase`, `Case1Claims'`, `Case2Claims'`,
  `StepStrands`, `StepFrame`, `stepStrands_of_frame`, `hagopian76_property4_step_cond2`,
  `hagopian76_theorem1_of_cases2` (over tight block sequences: `exists_thm1Setup_tight`,
  `hagopian76_theorem1_of_step_tight`).
* **§3.1 steps 1–2 and §3.2**: `Thm1Setup.kminus_isContinuum`, `Thm1Setup.kplus_isContinuum`,
  `Thm1Setup.half_bump`, `Thm1Setup.half_bump_side`, `closure_G_diff_E`.
* **§4.1 step 4**: `Thm1Setup.extension_misses_G` (and `GoodPoint.miss` is automatic:
  `Thm1Setup.comp_disjoint_G_of_ess`).

Still open after batch 182 (commented out at the end of `Hagopian76AA.lean`, or named `Prop`s; no
`sorry` in any declaration):
* **§1.3, the case split for `3 ≤ i ≤ m`** (`BlockLayersMeetSides3`). *Obstruction:* the route "on
  `Cl C`, `d` attains its least value only over the side segments" needs `d` monotone in the
  horizontal coordinate along `Cl C`; `lemma3_half` gives this inside one translate `h[E]` contained
  in `F`, but `Cl C` may meet several translates, and the layers of `F` through a translate not
  contained in `F` are not controlled. The weaker split holds for `d⁻¹(x₂)` (right region) and is open
  for `i ≥ 3`.
* **§3.1, `noncrossing_half_in_O`, steps 4–5.** *Obstruction:* `half_bump_side` places a frontier
  point of each half's component over a side segment; that the two halves reach *different* side
  segments (so that `W` crosses) needs S0 and the margin `8/n`, not formalized.
* **§3.3–§3.4 (commission 181 §1.2–§1.4): the points `zⱼ`, (iii) at `zⱼ`, §1.4 step 2, `τ₁ = 1`.**
  *Obstruction:* as in batch 181. For `τ₁ = 1`, Lemma 6's absorption gives only `d⁻¹(1) ⊆ R(X, E)`,
  already known; Lemma 4 would need the end piece `F ∩ hⱼ[k⁻¹((τ, 1])]` to be open in `F`.
* **2d, 2e, `innerComponentsCross_hagopian`.** *Obstruction:* the items above.
* **§4.1, E2.1 steps 1–3 and 5** (the first crossing component `Cᵢ₋₁`, the shortest extension `L`,
  `Cl Cᵢ₋₁` essential). *Obstruction:* the "argument similar to the one for Property 3" is for crossing
  components of `F`, not of `M`; an extension of `Cl Cᵢ` has no formal reason to come back over `D`.
* **§4.2, E2.4** (field `far`). *Obstruction:* the hypothesis "end sets within `ε₃`" of
  `Property2At` is not implied by `ρ(yᵢ₋₁, d⁻¹[I]) < ε₃` and `ρ(yᵢ, d⁻¹[I]) < ε₃`: `yᵢ` and `yᵢ₋₁` may be
  near `S_I` at different heights, and `L` misses `F`, so no end set of a subcontinuum of `L` is
  placed near the point of `d⁻¹[I]`. "`H` has a minimal admissible decomposition" also needs the
  restriction of the decomposition of `L` to a sub-interval.
* **§5, Case 2 (e)** (field `claim_e`). *Obstruction:* extending away from `Z` does not move the gap
  continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]`, which in Case 2 joins the two side segments; Property 2 for `f[N]`
  bounds how far `f[N]` reaches, not on which side of `S_J` `f(yᵢ₋₁)` lies.
* **The named `Prop`s** `StepFrame`, `LastStepClaims`, `BlockLayersMeetSides3`, `Case1Claims'`,
  `Case2Claims'`. *Obstruction:* the items above; also the two orientations with `d⁻¹[J]` on the side of
  `f(yᵢ)` (report §2.2).
* **`hagopian76_theorem1_final`.** *Obstruction:* by `hagopian76_theorem1_of_cases2`, exactly 2e and
  the five named `Prop`s.

---

## Batch 181: Hagopian 1976 XXVI (Theorem 1, saturation, 3c, Case 1 strand by strand, Case 2 sentence by sentence), items left open

**Closed in batch 181** (`HPC/Hagopian/Hagopian76Z.lean`, `H76Mid.lean`, `H76Block3c.lean`,
`H76Cap.lean`, `H76CapLow.lean`, `H76TipRel.lean`, `H76Thm1Setup.lean`; report
`doc/batches/REPORT-batch181.md`):
* **§3.1, the two fields**: `Thm1Setup.hε₃O`, `Thm1Setup.hε₃S` (`exists_eps_mid_O`,
  `exists_eps_mid_sides`, `exists_thm1Setup` restated); `f(y) ∈ π⁻¹[D]` for `y ∈ K`:
  `f_mem_O_of_mem_K`.
* **§3.2, the cap lemma**: `above_closure_misses_bottom`, `cross_strand_near`; the mirror
  `cross_strand_near_mirror` (with the extra hypothesis that the point is `ε₃`-far from `π⁻¹` of the
  bottom edge).
* **§2.1, 3c**: `block_components_cross` (with `InnerComponentsCross` as a hypothesis).
* **§2.2, E0, E1**: `property4_strand`, `property4_step_unless_setup` (frame forms
  `VFrame.property4_step_unless`, `VFrame.opposite_of_sepIn`).
* **§3.7, the ending of Case 1**: `case1_ending`; **§4 (c)**: inside `case2_ending`.
* **§3.8, §4, §5, conditional**: `case1`, `case2`, `hagopian76_property4_step_cond`,
  `hagopian76_theorem1_of_cases`.
* **§1.4 step 3** (`τ₁ < 1`): `tip_triod_mirror_rel` (the mirror triod needs only `2/n < σ < 1`),
  `chunk_edge_case_mirror`.

Still open after batch 181 (commented out at the end of `Hagopian76Z.lean`, or named `Prop`s; no
`sorry` in any declaration):
* **§1.1, `noncrossing_half_in_O`.** *Obstruction:* boundary bumping in the half `K⁻` needs the
  component of `K⁻ ∩ π⁻¹[D]` through `y` (a continuum in a non-closed half), and step 3 needs "the
  closure of `F − E` meets `E` only in `d⁻¹(e)`"; neither is formalized.
* **§1.2–§1.3, the points `zⱼ` and (iii) at `zⱼ`.** *Obstruction:* not formalized (void interior of
  `d⁻¹(1)` in `F` transported to `F ∩ U`; non-crossing of `Wⱼ` for large `j`; the strand lemma at
  `zⱼ`).
* **§1.4 steps 1, 2, 4.** *Obstruction:* steps 1–2 need §1.2–§1.3. Step 4 (`τ₁ = 1`) is undecided:
  the configuration is `d⁻¹(1) ⊇ F ∩ hⱼ[k⁻¹((τ, 1])]` with `F ∩ hⱼ[k⁻¹(1)] ≠ ∅`.
* **2d, 2e, `innerComponentsCross_hagopian`.** *Obstruction:* §1.1–§1.4. `InnerComponentsCross`
  stays a hypothesis of `hagopian76_theorem1_of_cases`.
* **`Case1Claims`** (§3.3 E2.1, §3.4 "between", §3.5 E2.4, §3.6 the band), fields of
  `Case1Witness`. *Obstruction:* E2.1 needs the first crossing component met by an extension of
  `Cl Cᵢ` (not formalized); §3.4 is blocked by the configuration of report 180 §4.5 (`L` leaves `D`
  through a side segment and re-enters on the other side of a strand's end); §3.5 needs the
  subcontinuum `H ⊆ L` with a minimal admissible decomposition; §3.6 needs "`N` is `ε₂`-far from `Q`",
  which the text argues only for `π⁻¹(p₄)`.
* **`Case2Claims`** ((a), (b), (d), (e)), fields of `Case2Witness`. *Obstruction:* (a), (b), (d) as
  in Case 1; for (e) nothing printed excludes `f(yᵢ₋₁)` below every `J`-strand when `yᵢ₋₁` is below
  `S_J` (configuration in report §4).
* **`BlockLayersMeetSides`** (the case split). *Obstruction:* not formalized; implicit in the text.
* **`hagopian76_theorem1_final`.** *Obstruction:* by `hagopian76_theorem1_of_cases`, exactly 2e and
  the three named `Prop`s above.

---

## Batch 180: Hagopian 1976 XXV (Theorem 1, the set-up repaired, saturation, 3c, the step), items left open

**Closed in batch 180** (`HPC/Hagopian/Hagopian76Y.lean`, `H76Cond4.lean`, `H76Tip.lean`,
`H76Thm1Setup.lean`; report `doc/batches/REPORT-batch180.md`):
* **§1.1, the certificate**: `property4_lower_false_of_K_eq`. With batch 179's `K = {p}`, Property 4
  fails for every block below the top, so the batch-179 step hypothesis could not be discharged.
* **§1.2, the repaired set-up**: `Thm1Setup` (with `K = {p} ∪ K₀`, `ε₂` as printed, `ε₃ ≤ θ/2`, the
  position clause, `n ≥ 40`, the composant data), `hagopian76_T15_T17_cond4`, `exists_thm1Setup`,
  `hagopian76_theorem1_of_step` (restated on `(3/22 + 8/n, 19/22 − 8/n)`).
* **§1.3, the positive check**: `Thm1Setup.K_meets_crossing`.
* **§2.1**: `tip_meets_end_layer`, `tip_meets_end_layer_mirror`, `tip_end_layer_continuum`.
* **2a** (with its mirror form) and **2b** (when the third arm is nonempty): `tip_triod`,
  `tip_triod_mirror`, `tip_triod_on_tip_layer`.
* **2c**: `degenerate_chunk_iii`.

Still open after batch 180 (commented out at the end of `Hagopian76Y.lean`; no `sorry` in any
declaration):
* **2d, `no_end_layer_chunk`.** *Obstruction:* not formalized. Missing: (1) step 2 of commission
  178 §3b ("`W` non-crossing, so one half `K⁻` or `K⁺` lies in `O`"), never formalized; (2) the
  points `zⱼ → c` with `d(zⱼ) < 1` and the non-crossing of their components for large `j`; (3) the
  transfer of (iii) to `zⱼ` with the §2.2 margin; (4) the edge case of 2b with an empty third arm.
* **2e, `innerComponentsCross_hagopian`** on `(3/22 + 8/n, 19/22 − 8/n)`. *Obstruction:* 2d and
  step 2 of commission 178 §3b. `InnerComponentsCross` stays a named hypothesis of
  `hagopian76_theorem1_of_step`.
* **3c, `block_components_cross`; E0, E1, `property4_step_unless`.** *Obstruction:* not formalized,
  also with `InnerComponentsCross` as a hypothesis: 3c needs `lemma3_half` in both directions along a
  crossing component; E0 and E1 need 3c.
* **§4, `Property4Step`** (E2.1, E2.4, the cap, E2.5, Case 2). *Obstruction:* not started beyond the
  set-up and the choice of `yᵢ₋₁ ∈ K` (`Thm1Setup.K_meets_crossing`). In addition, the bound of
  E2.5.2 ("the segment `[yᵢ₋₁, f(yᵢ₋₁)]` stays in `π⁻¹[D]`") is not added as a field: nothing in the
  choice of constants keeps `K` away from `π⁻¹[Fr D]` (the low vertical ends on the bottom edge, which
  is over `E`), so a uniform `ε₃` for all `yᵢ₋₁ ∈ K` is not available as stated (report §1.2).
* **`hagopian76_theorem1_final`.** *Obstruction:* by `hagopian76_theorem1_of_step`, exactly 2e and §4.

---

## Batch 179: Hagopian 1976 XXIV (Theorem 1, the end layer of `F`, `SepByCrossing` without conditions, uniform heights, the assembly, the step), items left open

**Closed in batch 179** (`HPC/Hagopian/Hagopian76X.lean`; report `doc/batches/REPORT-batch179.md`):
* **4.B** (batch 178): `p_on_crossing_piece` (with `Disjoint I₂ (π '' M)`, T7).
* **Nondegeneracy of the members of `I`** (batch 178): `crossingIntervals_nondegenerate`, from
  Property 3 as printed.
* **Finitely many crossing components** (2d.4): `crossing_components_finite`.
* **Uniform heights** (§4): the heights of Property 3, of "`I` is finite", of `x₂ₙ = 1` and of the
  middle-crossing lemmas are chosen before `G` (the `…_unif` theorems).
* **`SepByCrossing`, `x₂ₙ = 1`, Property 4 for the top block, from `InnerComponentsCross` alone**:
  `sep_by_crossing_uncond`, `hagopian76_x2n_eq_one_final`, `hagopian76_property4_top_final`.
* **The blocks** with only `x₂ₙ = 1` as a hypothesis: `exists_blocks_uncond`.
* **§7 of batch 178, `Thm1Setup` and Theorem 1 from the step**: `exists_thm1Setup` (T1–T13
  assembled), `hagopian76_theorem1_of_step` (with `InnerComponentsCross` as a second hypothesis).

Still open after batch 179 (commented out at the end of `Hagopian76X.lean`; no `sorry` in any
declaration):
* **2e, `InnerComponentsCross`** for every `Thm1Setup` (named `Prop`), with 2a, 2b, 2d.
  *Obstruction:* not formalized. Two points of the route need care (report §1.2): in 2d.5 the point
  `c` must lie over `(3/22 + 4/n, 19/22 − 4/n)` for "`c ∈ hⱼ[E]` implies `c ∈ Sⱼ`"; the triods of 2a,
  2b need `Z = Λ₁ ∪ h[k⁻¹(τ)]` to be a continuum, which needs `Λ₁` empty or meeting the tip layer.
* **3c, `block_components_cross`.** *Obstruction:* needs 2e.
* **§6, `Property4Step`** for every `Thm1Setup` and block sequence (E0, E1, E2.1–E2.6, Case 2).
  *Obstruction:* E0 and E1 need 3c; the rest is not started.
* **`hagopian76_theorem1_final`.** *Obstruction:* by `hagopian76_theorem1_of_step`, exactly 2e and
  §6.

## Batch 178: Hagopian 1976 XXIII (Theorem 1, the order of strands without Schoenflies, separation along the vertical, the end layer of `F`, unicoherence, the blocks), items left open

**Closed in batch 178** (`HPC/Hagopian/Hagopian76W.lean`; report `doc/batches/REPORT-batch178.md`):
* **S4 (batch 177), without Schoenflies**, in an abstract vertical frame `VFrame` and for crossing
  pieces of the concrete frame `lowFrame` (`isPiece_of_isCrossingPiece`):
  * S4a `crossing_piece_meets_sigma`; S4b `crossing_piece_sides`; S4c `crossing_piece_below_iff`;
    S4d `crossing_piece_below_trans`; S4e `crossing_piece_no_pocket`.
* **SSL**: `strand_separation`, its converse `strand_separation_converse`, the corollary
  `sepByCrossing_of_inner_crossing`.
* **The converse of Janiszewski's theorem** (batch-177 obstruction for the cap):
  `separatesPlane_union_of_inter_disconnected`; the domain form `sepIn_iff_separatesPts_union`.
* **3a, the end layer of `F`**: `T12Data.end_layer_not_subset`.
* **4.A, by composants**: `strand_misses_F_of_composant` (the companion `exists_T12Data_comp`).
* **4.C, conditional**: `sep_by_crossing` (`SepByCrossing` from `InnerComponentsCross` and crossing
  pieces through `p`, `f(p)` missing `F`).
* **C (§6), the blocks**: `exists_blocks`, with nondegeneracy of the members of `I` as a hypothesis.

Still open after batch 178 (commented out at the end of `Hagopian76W.lean`; no `sorry` in any
declaration):
* **3b, `InnerComponentsCross`** (named `Prop`). *Obstruction:* the configuration of route step 3.3,
  where `d⁻¹(1)` contains a chunk `h[k⁻¹((τ, τ₁))]` of the translate through `y` with `τ₁ ≥ k(e)`, is
  not excluded by the triod, by 3a, or by the void interior of `d⁻¹(1)` in `F` (report §3b); steps 1,
  2 and 3.1–3.2 are not formalized either.
* **3c, `block_components_cross`.** *Obstruction:* needs 3b, and `lemma3_half` in both directions
  along a crossing component.
* **4.B, `p`, `f(p)` on crossing pieces.** *Obstruction:* the strands of `p`, `f(p)` are crossing
  components (`strand_crossing`); that they are crossing pieces needs (i) closedness in `O` of a
  component of `M ∩ O` (routine) and (ii) that their closures miss `π⁻¹[I₂]`, which needs
  `I₂ ∩ π[M] = ∅`; the ends `F(3/22, r₂)`, `F(19/22, s₂)` of `I₂` lie on the side segments, where
  `IsCrossRegion` allows points of `π[M]`.
* **4.C, unconditional** (`x₂ₙ = 1`, Property 4 for the top block). *Obstruction:* 3b and 4.B.
* **C, nondegeneracy** of the members of `I` (no crossing component inside one layer). *Obstruction:*
  not addressed; a degenerate member would make an isolated zero-length block.
* **§7, `Thm1Setup` and `hagopian76_theorem1_of_step`.** *Obstruction:* not written; the bundle needs
  the constants of T1–T11 threaded to `hagopian76_I_finite`, `hagopian76_J_xs`,
  `hagopian76_x2n_eq_one` and `exists_T12Data_comp` with one `c₁`; skeleton in report §7.
* **§8 (E0–E2.6), `Property4Step`.** *Obstruction:* E0 and E1 need 3c; the cap (E2.3) is reduced to
  `separatesPlane_union_of_inter_disconnected` but the two-point intersection
  `d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∩ Q` and checks (α), (β), (γ) are not formalized; see
  `doc/notes/hagopian76-cases.md`.
* **`hagopian76_theorem1_final`.** *Obstruction:* waits on 3b, 4.B, nondegeneracy, §7 and §8.

## Batch 177: Hagopian 1976 XXII (Theorem 1, the strand lemma, the endgame rebuilt on it), items left open

**Closed in batch 177** (`HPC/Hagopian/Hagopian76V.lean`; report `doc/batches/REPORT-batch177.md`):
* **The strand lemma, S0–S3 and S6**:
  * `strand_fine_translate` (the structure `StrandConst`);
  * `strand_closure_subset`, `strand_crossing`, `strand_lemma`;
  * `strand_fine_positions`.
* **S5, whole strands**: `typeA'_inner_strands`.
* **The existence of `T12Data`** (batch-176 obstruction): `exists_T12Data`. T12 (2) holds for the `h`
  of T12 (3) (`strand_essential`).
* **`Y = π⁻¹[Fr D]`** (batch-176 assembly obstruction): `pi_preimage_frontier_D`.
* **The `N` versus `π⁻¹(p₄)` range obstruction** (batch 176): `15/22` lies in the inner middle, and
  S6 gives positions there.
* **The conditional assembly**:
  * `hagopian76_T15_T17_cond_fix` corrects the batch-176 `hagopian76_T15_T17_cond`, whose hypotheses
    are inconsistent (`T15_T17_cond_hyps_inconsistent`);
  * `hagopian76_T15_T17_cond2` discharges the package and `Y`.

Still open after batch 177 (commented out at the end of `Hagopian76V.lean`; no `sorry` in any
declaration):
* **S4, `strand_order`** (the linear order of strands; pockets miss the inner middle). *Obstruction:*
  * no Schoenflies homeomorphism of `Cl D` onto a square carrying the side segments to sides
    (`jordan_inner_collar` covers the collar, not `D`);
  * no cross-cut separation lemma for `D`.
* **S5, end strands as hairs.** *Obstruction:* needs `lemma3_half` along a small translate, together
  with S4.
* **C, the blocks of `St J`.** *Obstruction:* the finite merging of the members of `I` with
  `[0, e]` is not formalized.
  * *Finding:* the block hypothesis of the conditional forms (every member of `I` in some block) is
    already met by two coarse blocks.
  * A faithful C should require each block to be covered by members of `I`, with `Property4Step`
    restated for such blocks.
* **D, `SepByCrossing`.** *Obstruction:* the ladder argument and its converse need S4 and the hairs.
* **E, `Property4Step`.** *Obstruction:*
  * S4;
  * the cap `Λ` needs the converse of Janiszewski's theorem (two continua with disconnected
    intersection separate the plane), which is not formalized.
* **F, `hagopian76_theorem1_final`.** *Obstruction:*
  * waits on C, D and E;
  * also on the reduction of `Hagopian76Thm1` to the set-up T1–T11, with the strand constants chosen
    before `D`.

## Batch 176: Hagopian 1976 XXI (Theorem 1, the cutting step, positions by `ε₃`, Property 4, the induction, the assembly), items left open

**Closed in batch 176** (`HPC/Hagopian/Hagopian76U.lean`; report `doc/batches/REPORT-batch176.md`):
* **Positions by `ε₃`**: `eps3_positions_middle`, `eps3_image_middle` (points within `ε₃` of a point
  over the abscissa `1/2` lie over `(3/8, 5/8)`; Property 2 kept, `Property2At.mono`). The
  batch-175 obstruction "the induction needs `L₆`" is removed at the sentence "`f(yᵢ₋₁)` belongs to
  `L₆ ∩ π⁻¹[D]`".
* **Janiszewski inside a domain**: `sepIn_union_cases`.
* **`TailCutKeepsSep` and `x₂ₙ = 1`, reduced** to the named `Prop` `SepByCrossing`
  (`sep_by_crossing_cut`, `hagopian76_x2n_eq_one`).
* **Property 4 for the top block**, from `SepByCrossing`, on a `T12Data`
  (`hagopian76_property4_top`).
* **The closing contradiction, conditional**: `hagopian76_T15_T17_cond`.

Still open after batch 176 (commented out at the end of `Hagopian76U.lean`; no `sorry` in any
declaration):
* **`SepByCrossing`** (`def … : Prop`, `HPC/Hagopian/H76Cut.lean`). *Obstruction:*
  * `sepIn_union_cases` splits only two compact pieces that do not meet inside `π⁻¹[D]`, and the
    crossing components and the rest of `G ∩ π⁻¹[D]` are not of that form;
  * components of `G ∩ π⁻¹[D]` meeting `d⁻¹(1)` may reach the middle (P3's exception);
  * route 2, the classification of the components of `π⁻¹[D] − G`, is not formalized.
* **The existence of `T12Data`** (structure, `HPC/Hagopian/H76Prop4.lean`). *Obstruction:* T12 (2)
  is proved for T9's `h′` (`hagopian76_T12_parts12`), not for the `h` of T12 (3)
  (`hagopian76_T12_uncond`).
* **`Property4Step`** (`def … : Prop`, `Hagopian76U.lean`), Cases 1–2. *Obstruction:*
  * "first component" needs the extensions of `Cl Cᵢ` as type A′ continua compatible with `D`, and
    the order of crossing components along them;
  * `N` versus `π⁻¹(p₄)`: P3 controls `L` only over `[3/8, 5/8]`, while `p₄` is at `15/22`;
  * the separation by `P ∪ Q` is route 2.
* **The assembly** `hagopian76_theorem1_final`. *Obstruction:* waits on the above, on `Y = π⁻¹[Fr D]`
  (compact, connected), on the blocks of `St J` from the finite `I`, and on the assembly of the
  set-up T1–T11 from `¬` hereditary indecomposability.

## Batch 175: Hagopian 1976 XX (Theorem 1, components through the middle, no deep pockets, `x₂ₙ = 1`, Property 4, the induction, the assembly), items left open

**Closed in batch 175** (`HPC/Hagopian/Hagopian76T.lean`; report `doc/batches/REPORT-batch175.md`):
* **Pockets at the middle** (batch-174 obstruction; batch-173 `CoverPocket`, partly):
  `component_over_middle_crossing` (every component of `F ∩ π⁻¹[D]` through a point over the
  abscissae `[3/8, 5/8]` is crossing or meets `d⁻¹(1)`), `component_over_middle_crossing_of_end`,
  `cover_pocket_middle`. `CoverPocket` as stated over `L₆` is not covered.
* **P2**: `translate_through_point_in_F`.
* **`x₂ₙ = 1`, reduced**: `hagopian76_tail_middle` and `hagopian76_x2n_eq_one_of_cut`
  (`TailCutKeepsSep → LastIntervalReachesOne` for Hagopian's irreducible `F`).

Still open after batch 175 (commented out at the end of `Hagopian76T.lean`; no `sorry` in any
declaration):
* **`TailCutKeepsSep`** (`def … : Prop`, `HPC/Hagopian/H76X2n.lean`): cutting `F` beyond every
  interval of `I` keeps the separation. *Obstruction:* the tail meets the middle only in components
  reaching `d⁻¹(1)` (`hagopian76_tail_middle`). Two questions remain:
  * whether a shallow tail component touching a side segment can be part of a barrier between two
    middle points. This is plane separation (Janiszewski, compact form); the project has Janiszewski
    only for polygonal sets;
  * whether Hagopian's `F` can end over the middle.
* **Property 4 for `[x₂ₙ₋₁, x₂ₙ]`.** *Obstruction:* clause (2) is the cutting step for the gaps
  between blocks too; clause (1) needs the T12 set-up.
* **The induction, Cases 1 and 2.** *Obstruction:* the pockets are controlled only over `[3/8, 5/8]`,
  while the induction needs `L₆`, over `(5/11 − η, 8/11 + η)`. The margin comes from the one-eleventh
  scale of `IsEps1`. `N` and `ε₂` are unchanged from batch 174: Property 3 is needed for an extension
  of `Cl Cᵢ`.
* **The assembly.** Waits on the above; the only conditional form is
  `hagopian76_x2n_eq_one_of_cut`.

## Batch 174: Hagopian 1976 XIX (Theorem 1, "`I` is finite", the end element, `J` and the `xᵢ`, Property 4, the induction, the assembly), items left open

**Closed in batch 174** (`HPC/Hagopian/Hagopian76S.lean`; report `doc/batches/REPORT-batch174.md`):
* **Property 3 for the end element `d⁻¹(1)`** (batch-173 item): `hagopian76_property3_end_element`
  (thin-strip form, every layer `v ∈ [0, 1]`) and `hagopian76_property3_components` (the printed
  statement, every element of the decomposition), through a proper extension
  (`exists_end_extension`, `property3_layer_all`).
* **"`I` is finite"** (batch-173 item): `hagopian76_I_finite`, with `crossingIntervals_disjoint`
  (distinct members of `I` have disjoint interiors) and the length bound in every layer
  (`crossing_length_pos_all`).
* **`x₁ = 0`, `x₂ = e`**: `hagopian76_J_xs` (`e < x` for every `[x, y] ∈ I`).
* **"`[x₁, x₂]` does not have Property 4"**: `hagopian76_property4_base`.

Still open after batch 174 (commented out at the end of `Hagopian76S.lean`; no `sorry` in any
declaration):
* **`x₂ₙ = 1`** (`LastIntervalReachesOne`, a `def … : Prop`). *Obstruction:* the natural argument
  cuts off the tail `d⁻¹((y*, 1])` beyond the last crossing block and appeals to the irreducibility
  of `F` (T13). The tail still meets `π⁻¹[D]` in components that are not crossing components (their
  closures miss a side segment), and such a component can still separate `π⁻¹[D]` (a pocket at one
  side). So the cut need not keep the separation, and irreducibility gives nothing. The statement is
  false for a general extension (`G = E` gives `I = ∅`).
* **Property 4 for `[x₂ₙ₋₁, x₂ₙ]`** (`hagopian76_property4`). *Obstruction:* clause (2), "only the
  last block separates", needs to drop the other blocks while keeping the separation, which meets
  the same pockets of non-crossing components as `x₂ₙ = 1`; clause (1) needs the point `yₙ ∈ K` and
  the essential-continuum set-up of T12, which is not threaded into the statement.
* **The induction, Cases 1 and 2** (`hagopian76_property4_step`). *Obstruction:* the pockets in
  "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below `d⁻¹[J]`" (the strands of the layers of `F`
  bounding a pocket are not translates of short pieces of `E`, so coarse monotonicity does not
  bound them), and "`N` does not come within `ε₂` of `π⁻¹(p₄)`" (needs Property 3 and the
  first-component argument for the extension `L` of `Cl Cᵢ`, not of `E`).
* **The assembly** (`hagopian76_theorem1_final`). Waits on the three items above; no conditional form
  is stated.
* Carried over: the pockets of the covering half (`CoverPocket`) and the ends of crossing components
  (`CrossingEnds`), batch 173.

## Batch 173: Hagopian 1976 XVIII (Theorem 1, Property 3 by descent, pockets, ends of crossing components, T15–T17), items left open

**Closed in batch 173** (`HPC/Hagopian/Hagopian76R.lean`; report `doc/batches/REPORT-batch173.md`):
* **Property 3** (batch-172 item, via `Property3End`): proved unconditionally by descent,
  `hagopian76_property3` (thin-strip form, conclusion of `hagopian76_property3_of_end` without the
  hypothesis `Property3End` and without `0 < v`) and `hagopian76_property3_domain` (Hagopian's form,
  over `D`). D1: `crossing_from_layer_translate`; D2: `crossing_descends`; the closed set of crossing
  parameters: `isClosed_layerCrossing`. `Property3End` itself is not proved and is no longer needed.
* **A length bound for crossings** (toward "`I` is finite"): `crossing_length_pos`.

Still open after batch 173 (commented out at the end of `Hagopian76R.lean`; no `sorry` in any
declaration):
* **Property 3 for the end element `d⁻¹(1)`.** *Obstruction:* the swallowing lemma (hence
  `hagopian76_property3_translate`) needs an interior layer, and the shift of Lemmas 2–3 needs
  `v < 1`.
* **The covering half, pockets** (`CoverPocket`, `crossing_sides_cover'`). *Obstruction:* coarse
  monotonicity (`IsEps1.sep_of_gap`) puts a point of `Cl Cᵢ₋₁ ⊆ h′[E]` over abscissa `t` in `h′` of a
  piece adjacent to that of `t`. A pocket reaching the middle abscissae may be bounded by two strands
  lying in `h′` of the same middle pieces. Nothing makes the pieces of `E` small, so this is not
  excluded.
* **The ends of crossing components** (`CrossingEnds`, `crossing_component_ends`). *Obstruction:*
  T17's "`N` does not come within `ε₂` of `π⁻¹(p₄)`" concerns the subcontinuum `N` of the shortest
  extension `L` of `Cl Cᵢ` containing `Cᵢ₋₁`. D1 controls the ends of one translate `ψ[E]`, not `L`.
* **"`I` is finite"** (`hagopian76_I_finite`). *Obstruction:* Property 3 gives a positive lower bound
  on the lengths of the intervals of `I` below any `v₀ < 1` (`crossing_length_pos`), and the
  intervals are pairwise non-nested. That does not bound their number: overlapping intervals of
  length `≥ λ` can accumulate, and components of `F ∩ π⁻¹[D]` can accumulate (`F` is not locally
  connected).
* **Property 4, its induction, T15–T17 and `hagopian76_theorem1`.** Not formalized, even
  conditionally.

## Batch 172: Hagopian 1976 XVII (Theorem 1, the end case of Property 3, the `I₂` case and side edges by Schoenflies, ends of crossing components, T15–T17), items left open

**Closed in batch 172** (`HPC/Hagopian/Hagopian76Q.lean`; report `doc/batches/REPORT-batch172.md`):
* **The end case of Property 3** (batch-171 item). Swallowing lemma: `continuum_subset_layer_of_open`.
  A layer containing a crossing contains the whole translate `h[G]` of the extension:
  `hagopian76_property3_translate`. Property 3 is reduced to the named `Prop` `Property3End`:
  `hagopian76_property3_of_end`.
* **`Property3End`, conditionally:** from `Cl R(E) = M` (`property3End_of_closure_Rset`) and from
  the dichotomy (`property3End_of_dichotomy`), both through `closure_Rset_subset_of_translate`.
* **The covering half, `I₂` case** (batch-171 item): `top_component_above_aux`, with the bottom case
  in `crossing_sides_cover_schoenflies`. The inner collar of an arc of a Jordan curve:
  `jordan_inner_collar`.

Still open after batch 172 (commented out at the end of `Hagopian76Q.lean`; no `sorry` in any
declaration):
* **`Property3End`** (`property3_end`), hence Property 3 itself. *Obstruction:* an
  `ε₁`-homeomorphism `h` with `h[G] ⊆ d⁻¹(v)` puts `Cl R(E)` in one layer of `h⁻¹[G]`. This is
  contradictory if `Cl R(E) = M` or under the dichotomy, both open (batch 169, C.1). Otherwise
  nothing available excludes a proper indecomposable `Cl R(E)` with `h[Cl R(E)] ⊆ d⁻¹(v) ⊆ G`. The
  homeomorphism is given by `follows_crossing` and preserves the composant of `E`, so the composant
  argument of batch 171 does not apply.
* **The covering half, side edges and pockets** (`crossing_sides_cover'`). *Obstruction:* a component
  of `π⁻¹[D] − Z` whose closure meets the frontier of `D` only in a side segment, between two points
  of `Z` (a pocket), is neither above nor below `Z`. Non-separation does not exclude pockets, and
  link control does not keep `L₆` out of them. Hagopian's sentence "Hence `f(yᵢ₋₁)` is either above
  `d⁻¹[I]` or below `d⁻¹[J]`" does not address this case. Proposed named `Prop`: `CoverPocket`.
* **The ends of a crossing component** (`crossing_component_ends`). *Obstruction:* unchanged from
  batch 171. Item A no longer passes through the end links, so it gives nothing here.
* **T15–T17 and `hagopian76_theorem1`.** Not reached. "`I` is finite", Property 4 and its induction,
  and the first-component argument are not formalized, even conditionally.

## Batch 171: Hagopian 1976 XVI (Theorem 1, Property 3 without margins, side edges, ends of crossing components, the dichotomy), items left open

**Closed in batch 171** (`HPC/Hagopian/Hagopian76P.lean`; report `doc/batches/REPORT-batch171.md`):
* **The dichotomy is no longer needed** (batch-169/170 item): `translate_Rset_disjoint` (a
  homeomorphism moving a point of `E` off its composant carries `R(E)` off `R(E)`) and
  `hagopian76_T12_uncond` (T12, conditions 2–3, without `RsetDichotomy`). The dichotomy itself is
  not proved.
* **The covering half, bottom case** (`crossing_bottom_below`).
* **Property 3, partial:** reduced to an end case (`layer_meets_translate_end`,
  `hagopian76_property3_reduced`).

Still open after batch 171 (commented out at the end of `Hagopian76P.lean`; no `sorry` in any
declaration):
* **Property 3, the end case** (`hagopian76_property3`). *Obstruction:* a layer `d⁻¹(v)` of `F`
  containing a crossing may meet every translated layer `h[k⁻¹(t)]` with `t ≤ 6/11` (or every one
  with `t ≥ 5/11`), reaching the end links `L₀` (or `L₁₀`). Lemma 3 says nothing there (its
  hypothesis that the layer misses the translated end sets fails); the triod of route A.2 needs
  `h[E] ∩ F ⊆ d⁻¹(v)`, which fails when `h[E] ∩ F` runs along `F` past `d⁻¹(v)`; route A.1 needs
  closedness of a parameter set defined through homeomorphisms, which do not converge.
* **The covering half, `I₂` case and side edges** (`crossing_sides_cover'`). *Obstruction:* the
  `I₂` case needs a connected inner neighbourhood of the arc `I` in `D′` (local connectedness of
  `Cl D′` along an arbitrary arc; not in the project); the side-edge positions `belowSet′`,
  `aboveSet′` need a version of `rect_domain_crossing_separates` with anchors on the frontier; the
  pockets are unchanged from batch 170.
* **The ends of a crossing component** (`crossing_component_ends`). *Obstruction:* `follows_crossing`
  controls only `(4/11, 7/11)`; Lemma T's `δ` is chosen after `D` while `ε₁` is fixed before;
  refining the chain means re-running Property 1 with the 11 hard-wired in `chainG`, `piece`,
  `elev`, `EndCtl`.
* **T15–T17 and `hagopian76_theorem1`** (now unconditional in shape): wait on the above.

## Batch 170: Hagopian 1976 XV (Theorem 1, `ExtChainInter`, the covering half, "follows", Property 3), items left open

**Closed in batch 170** (`HPC/Hagopian/Hagopian76O.lean`; report `doc/batches/REPORT-batch170.md`):
* **`ExtChainInter`** (`extChainInter`; inside one extension, `extChainInter_in`): closes the
  batch-169 item. **T13 unconditional** (`hagopian76_T13_uncond`).
* **"Follows" for crossing components** (`follows_crossing`): the closure of a crossing component
  contains `h[k⁻¹((4/11, 7/11))]`, `h` an `ε₁`-homeomorphism with Property 1's link condition.
* **The covering half, first step** (`crossing_sides_cover_frontier`).
* **`crossing_set_closed`** with margins, and the least `v` (`hagopian76_first_crossing_param`).

Still open after batch 170 (commented out at the end of `Hagopian76O.lean`; no `sorry` in any
declaration):
* **The covering half, the three cases** (`crossing_sides_cover`). *Obstruction:* the bottom case
  needs a low strip in collar coordinates below `K`, connected after removing `K`, reaching the
  vertical (the bottom edge contains layers of `E`, where `π` is not injective); the `I₂` case needs a
  thin neighbourhood of `I₂` minus `K` to be connected; pockets bounded by `K` and a side segment are
  not excluded by non-separation and can reach `L₆`. Positions must be redefined through the side
  edges (report §1.B, §5).
* **Property 3** (`hagopian76_property3`). *Obstruction:* the shift `g` loses the margin: `g[Q]`
  crosses with margin `μ − δ`, so the least `v` for margin `μ` is not contradicted. The margin-free
  route through Lemma T in `d⁻¹(u)` needs a translate of a middle range wider than `[3/22, 19/22]`
  (item C gives `(4/11, 7/11)`) and Lemma T for the `(δ + ε₁)`-small `g ∘ h`.
* **"Follows", strengthened**: that the ends of a crossing component lie in `L₂` and `L₁₀` (needed in
  T17 for "`N` does not come within `ε₂` of `π⁻¹(p₄)`").
* **The dichotomy** (`Rset_homeo_dichotomy`) and **`Cl R(E) = M`**: unchanged from batch 169; not
  attempted.
* **T15–T17 and `hagopian76_theorem1_cond`**: wait on the above.

## Batch 169: Hagopian 1976 XIV (Theorem 1, above/below, generic `p`, `q`, the dichotomy, T13, Property 3), items left open

**Closed in batch 169** (`HPC/Hagopian/Hagopian76N.lean`; report `doc/batches/REPORT-batch169.md`):
* **`R(E)` is meagre** (`isMeagre_Rset`): `R(E)` lies in the composant of a point of `E`.
* **Above and below a crossing continuum, disjointness half** (`crossing_sides`; `belowSet`,
  `aboveSet`, both open).
* **`p`, `q` off `R(E)`** (`exists_generic_pq`). This closes the batch-168 item. The points are not
  on `K₀`: they are taken in the open sets below and above the crossing continuum near the batch-168
  points of `K₀`. `H` (and `R(E)`) separates them, and their components cross.
* **The dichotomy from `Cl R(E) = M`** (`Rset_homeo_dichotomy_of_closure`), and the dichotomy as a
  hypothesis (`RsetDichotomy`, C.3) with its consequence for T12
  (`hagopian76_T12_of_dichotomy`: conditions 2–3 of report 168 §1.A).
* **T13, the compactness half** (`iInter_chain_extension`: the intersection of a chain of separating
  extensions is a continuum containing `E` and still separates), and **T13 under `ExtChainInter`**
  (`hagopian76_T13`, Zorn).

Still open after batch 169 (commented out at the end of `Hagopian76N.lean`; no `sorry` in any
declaration):
* **The dichotomy** (`Rset_homeo_dichotomy`). *Obstruction:* route C.1 needs `Cl R(E) = M`, which is
  open; route C.2 needs, for a translate `g[F]` meeting `R(E)`, a piece of the line `R(E)` with an
  end set missing `g[F]`. Absorption (`subset_extUnion_of_meets`) handles every continuum through
  the meeting point that misses `k⁻¹(0)` or misses `k⁻¹(1)`. The remaining case is a continuum in
  `g[R(E)]` that contains `E`; it is not excluded.
* **`Cl R(E) = M`** (`closure_Rset_eq_univ`). No argument either way.
* **`ExtChainInter`**: that the intersection of a chain of separating extensions away from
  `k⁻¹(0)` is again of type A′ with end set `k⁻¹(0)`. *Obstruction:* irreducibility and an
  admissible decomposition of the intersection; by `ext_layers` each extension `≠ E` is `d⁻¹[[0, s]]`
  of a larger one, but a decreasing chain need not have a last layer.
* **A, covering half**: that every point of `π⁻¹[D] − Z` is below or above `Z`. *Obstruction:*
  false for arbitrary crossing continua. If `Z` encloses a bubble (for example a crossing arc
  together with a small circle attached to it), the inside of the bubble is neither below nor above
  `Z`. This was found by informal reasoning and is not formalized. For `Z ⊆ M` it needs `Z` not to
  separate the plane. T17 uses the covering at "Hence `f(yᵢ₋₁)` is either above `d⁻¹[I]` or below
  `d⁻¹[J]`".
* **Property 3** (`crossing_set_closed`, `hagopian76_property3`): as after batch 168. Not
  attempted.
* **F** (`follows_essential_crossing`). *Obstruction:* the component `Cᵢ₋₁` is fixed by `Cl Cᵢ`, so
  its points cannot be chosen generically, and Lemma T covers it only if it contains a point `h′(x′)`
  low over the middle range.
* **T15–T17 and `hagopian76_theorem1`**: wait on the above.

## Batch 168: Hagopian 1976 XIII (Theorem 1, Lemma R, T12 (3), Property 3, T13–T17), items left open

**Closed in batch 168** (`HPC/Hagopian/Hagopian76M.lean`; report `doc/batches/REPORT-batch168.md`):
* **Lemma R** (`crossing_piece_of_R`): crossing pieces of `R(X, E)`, disjoint from `E`, through
  points of `R(X, E) − E` arbitrarily close to any `x ∈ E` over the middle range, each inside one
  extension of `E` away from `k⁻¹(0)`. This closes batch-167 obstruction 2 ("crossing continua *in*
  `R(E)`").
* **Crossing continua cut `D`** (`crossing_separates`, `crossing_pair_separates`).
* **T12 (3), in a shape** (`hagopian76_T12`): a crossing continuum of `R(X, E)` separates
  `p = h₀(x)` from `q = h₁(x)` on `K₀` in `π⁻¹[D]`.

Still open after batch 168 (commented out at the end of `Hagopian76M.lean`; no `sorry` in any
declaration):
* **`p`, `q` off `R(E)`.** Report §1.A shows this is the only condition on `p`, `q` that T13–T17
  use. *Obstruction:* no argument gives a point `h(x)` low on `K₀` near `x` with `h[R(E)] ≠ R(E)`.
  Meagreness of `R(E)` does not help: `M ∩ K₀ ∩ W` can be meagre in `M`.
* **The dichotomy** "`g[R(E)] ∩ R(E) ≠ ∅ ⇒ g[R(E)] = R(E)`", which Hagopian uses tacitly in T17 (and
  to get T12 (2) for his `h`). *Obstruction:* not proved. `R(E)` is a composant of `Cl R(E)`, but
  `g[Cl R(E)]` need not equal `Cl R(E)`.
* **Property 3** (`crossing_set_closed`, `hagopian76_property3`): as after batch 167. Not attempted.
* **T13**: *obstruction:* `p`, `q ∉ H` for the extension `H` holding the separating piece, and the
  irreducible element (an intersection of a chain of separating extensions is an extension).
* **T15–T17 and `hagopian76_theorem1`**: wait on the above. T17's low point of `Cᵢ₋₁` needs "the
  chain follows `Cl C`" for every crossing component `C` essential to `h[R(E)]` (report §1.E).
* **`Cl R(E) = M`?** Not settled. By report §1.A it is no longer needed.

## Batch 167: Hagopian 1976 XII (Theorem 1, crossing translates, T12, Property 3, T13–T17), items left open

**Closed in batch 167** (`HPC/Hagopian/Hagopian76L.lean`; report `doc/batches/REPORT-batch167.md`):
* **Lemma T** (`crossing_translate`). Take a small homeomorphism `h` with `h(x)` above the axis and
  off `E`. Then `h[k⁻¹[[a′, b′]]]` misses `E` and lies in the collar band above the axis, layer by
  layer. The component of `M ∩ π⁻¹[D]` through `h(x)` contains the middle layers and is crossing.
* **Lemma T′** (`K0_dense_low`): Hagopian's `x ∈ k⁻¹(p₃) ∩ Cl(M ∩ K₀)`. This closes the batch-166 point
  "that crossing components meet `K₀` near `x`".
* **T12 (1)–(2), in a shape I chose** (`hagopian76_T12_parts12`, `crossing_essential`). The
  essential translate is T9's `h′`, not the `h` with `h(x) = p`.

Still open after batch 167 (commented out at the end of `Hagopian76L.lean`; no `sorry` in any
declaration):
* **T12 (3) and the choice of `p`, `q`.**
  * *Obstruction 1:* no argument that two of the points `p = h(x)` of Lemma T′ lie off `R(E)` in
    distinct composants of `Cl R(E)`. The countability route of commission 167 needs a property
    specific to `M`: a proper subcontinuum can contain uncountably many disjoint crossing continua.
    Whether `Cl R(E) = M` is not settled.
  * *Obstruction 2:* "R(E) separates these components in π⁻¹[D]" needs crossing continua *in
    `R(E)`* near `E`. Lemma T gives translates `h[E]`, which are not known to lie in `R(E)`.
* **Property 3** (`crossing_set_closed`, `hagopian76_property3`): as after batch 166 (attainment of
  the least `v`; the shift `g` with a margin). The continuum form of "crossing" should suffice for
  T15–T17 (report §1.C).
* **T13**: waits on T12 (3).
* **T15–T17 and `hagopian76_theorem1`**: wait on the above. For T17, Lemma T gives "follows
  `Cl Cᵢ₋₁`" only if `Cᵢ₋₁` has a point low enough over the middle range.
* **T9, "follows `Cl B`", in general**: open, as after batch 166.

## Batch 166: Hagopian 1976 XI (Theorem 1, `D`, `K₀`, Property 3, T12–T17), items left open

**Closed in batch 166** (`HPC/Hagopian/Hagopian76K.lean`; report `doc/batches/REPORT-batch166.md`):
* **`D` as a Jordan domain** (T8): `rect_domain` and `hagopian76_D`. This closes the batch-165 item
  "`D` as a Jordan domain".
* **`K₀`**, the low part of `K` (T11): `hagopian76_K0`. It is a component of
  `π⁻¹[D ∩ ⟨p₃, q₃⟩]`, connected, misses `E`, and its closure meets `k⁻¹(p₃)` and `π⁻¹[I₂]`.
  Also proved: **`K₀` is a cross-cut of `D`** (`hagopian76_K0_crosscut`).
* In T12, two composants different from `R(E)` exist in every open set, without Mazurkiewicz
  (`exists_two_composants_in_open`).

Still open after batch 166 (commented out at the end of `Hagopian76K.lean`; no `sorry` in any
declaration):
* **T11 for the single component `K`, as printed** (separating `L₂` from `L₁₀`).
  * *Obstruction:* the channel objection of batch 165, which the commission accepted.
  * The separation is carried by `hagopian76_T11` for the whole section. The side-edge separation
    by `K₀`, which T12 and T17 use, is proved.
* **T9, "the chain `L − {L₁, L₁₁}` follows `Cl B`".**
  * *Obstruction:* the end of `Cl B = h[G]` at `u = min k[G]` is `h[G ∩ k⁻¹(u)]`, part of a layer.
    Boundary bumping keeps a continuum through a point of it inside `B`, but possibly inside that
    layer. To conclude, one needs `G ∩ k⁻¹(u) ⊆ Cl k⁻¹[0, u)`, which is not argued (report §1.C).
  * The one-link margin at `L₄` is repaired by restricting to components through `K₀`, which is all
    that T12 and T17 use.
* **Property 3.**
  * *Obstruction:* (i) the least `v` must be attained. The limit continuum `Z` misses `E` and
    `π⁻¹[I₂]`, but that a component of `Z ∩ π⁻¹[D]` reaches *both* sides is not proved.
  * (ii) "`L` follows a type A′ continuum in `d⁻¹(v)`" needs item C.
  * (iii) The crossing property under the shift `g` needs a margin: `g[Q]` may meet `E` or fall short
    of the side edges. Report §1.D proposes a shape.
* **T12.**
  * *Obstruction:* points of `Cl R(E)` on `K₀` near `x`, in two composants other than `R(E)`.
    Crossing components meet `K₀` (cross-cut lemma), but their existence near `x` is item C, and
    that they meet `K₀` near `x` is not argued.
  * Proposed: choose `x` in `Cl(K₀ ∩ Cl R(E))`.
  * "By Property 1, `R(E)` intersects an arc in `K` …" is unargued.
* **T13, T15–T17 and `hagopian76_theorem1`.** Wait on C, Property 3 and T12. Shapes are in report
  §5.

---

## Batch 165: Hagopian 1976 X (Theorem 1, T7–T17), items left open

**Closed in batch 165** (`HPC/Hagopian/Hagopian76J.lean`, report `doc/batches/REPORT-batch165.md`):
* **T7** (`hagopian76_T7`), by the crossing route of commission 165 §1: no hair on `E`
  (`hagopian76_no_hair`), preimages of continua under `π` (`preimage_pi_isContinuum`), the crossing
  lemma (`rect_crossing`). This closes the batch-164 item "T7, the arc `A` and `I₂`" (the arc `A` and
  `h[E]` are no longer needed).
* **Link control** (`exists_isEps1_endCtl`, `hagopian76_link_control`).
* **T8 as property (D)** (`hagopian76_T8`), **T9 in full** (`hagopian76_T9_full`), except the
  sentence "the chain `L − {L₁, L₁₁}` follows `Cl B`".
* **T11** (`hagopian76_T11`), with `K` replaced by the whole of `π⁻¹[D ∩ ⟨p₃, q₃⟩]`.

Still open after batch 165 (commented out at the end of `Hagopian76J.lean`, no `sorry` in any
declaration):
* **`D` as a Jordan domain** (T8). *Obstruction:* not needed for T9 and T11 in the shapes proved,
  which hold for every `D` inside the thin strip; Property 3 needs `D`'s two side edges
  `⟨p₁, r⟩`, `⟨p₅, s⟩`, so `D` has to be built from `I₂` and the three segments, with the
  Jordan curve theorem (`HPC/Jones`) and the inclusion `D ⊆` strip.
* **T11 with the single component `K`.** *Obstruction:* if `I₂` doubles back over the vertical
  `⟨p₃, q₃⟩`, a part of `D` above the first crossing can reach both sides of `K` (report 165 §2.D);
  the printed sentence gives no argument. Whether T12–T13 need `K` connected is open.
* **T9, "the chain `L − {L₁, L₁₁}` follows `Cl B`".** *Obstruction:* needs `Cl B` to reach both
  verticals (the crossing property of Property 3).
* **Property 3.** *Obstruction:* (i) the least `v`: a hyperspace limit of crossing continua
  (report 164 §1.6); the limit misses `E` by `hagopian76_no_hair` and `π⁻¹[I₂]` by `ε₂`, but that it
  is again a crossing continuum inside one layer of `F` is not proved; (ii) the crossing property of
  `g[Q]` under the shift `g` (`hagopian76_property3_shift`). Both need `D` as a domain.
* **T12, T13, T15–T17 and `hagopian76_theorem1`.** Wait on Property 3 (shapes: report 164 §5,
  revised in report 165 §5).

---

## Batch 164: Hagopian 1976 IX (Theorem 1, T7–Property 3), items left open

**Closed in batch 164** (`HPC/Hagopian/Hagopian76I.lean`, report `doc/batches/REPORT-batch164.md`):
* **The reparametrization** (`hagopian76_reparam`): batch-163 item "T6 at Hagopian's abscissae".
* T6 at `[3/22, 19/22]` (`hagopian76_T6_placed`, `hagopian76_I1`).
* In T7, the points of `π[M]` above `π[E]` (`M_meets_above`) and the accessible point `y` above
  (`hagopian76_T7_accessible`).
* The positivity in `ε₂` (`hagopian76_eps2_pos`).

The open statements of the skeleton are kept, never as declarations, in a comment block at the end of
`Hagopian76I.lean`.

Still open after batch 164:
* **T7, the arc `A` and `I₂`.** *Obstruction* (report 164 §1.2):
  1. `h[E]` (Property 1, `y ∈ h[E]`) has to be set up as a type A′ continuum with `y` in an interior
     layer. This needs transport of `IsMinimalAdmissible` along `h`, and `y` far from the end sets.
  2. Its quotient `π′`, `γ′` and collar come from `exists_quotient_plane'_aux` and
     `exists_collar_vertical`, and its strip from `hagopian76_T6`. These are available but not
     assembled.
  3. The strip has to lie on the side of `h[E]` facing `π[E]`, close to `π[E]`. This is not argued
     in print.
  4. The unargued sentence "By choosing `y` sufficiently close …". Proposed route: a collar strip
     over `[3/22, 19/22]` inside `π[St L]` (uniform height), with `π[A]` inside it.
* **T8** (`D`): needs `I₂`. Then use the Jordan curve theorem; property (D) follows from the strip.
* **T9 in full:** needs `D`. Its first sentence is `hagopian76_T9` (batch 161), and `ε₂ > 0` is
  `hagopian76_eps2_pos`.
* **T11:** needs `D` and link control: `π[L₂ ∩ π⁻¹[D]]` left of abscissa `7/22`, `π[L₁₀ ∩ π⁻¹[D]]`
  right of it (report 164 §5).
* **Property 3:** needs `D`. Also open: the least `v` (a hyperspace limit argument is proposed in
  report 164 §1.6) and the crossing property under the shift `g`.
* T3 at the end layers: as in batch 163 (not used).

---

## Batch 163: Hagopian 1976 VIII (collar geometry), items left open

**Closed in batch 163** (`HPC/Hagopian/Hagopian76H.lean`, report `doc/batches/REPORT-batch163.md`):
item A, `exists_collar_adapted` (skeleton shape); item B, `no_M_below` (both sides; the skeleton's
unused hypothesis `a ≤ b` dropped); item C, **Lemma 9** (`hagopian76_lemma9`, skeleton shape); item D,
**T6** (`hagopian76_T6`; the skeleton's unused premise `a ≤ b →` dropped). This closes batch-162 items
B and T6, batch-161 item 6, batch-160 item E, batch-159 item E and batch-158 item F (the
commented-out copies in `Hagopian76C`–`G.lean` are replaced by one-line pointers). Nothing in this
batch is commented out.

Still open after batch 163:
* **T7** (optional in commission 163; not attempted). Obstruction unchanged from batch 162 (below):
  an accessible point of `M ∩ L₆` above `π[E]` and the same core argument on the upper side of the
  collar, for `h[E]`; control of the links of `L` in collar coordinates. The core argument of this
  batch (`no_M_below_core`) is written for the lower side and for `E` itself.
* **T6 at Hagopian's abscissae.** `hagopian76_T6` gives the strip below `γ([a, b])` for every
  `[a, b] ⊆ (0, 1)` avoiding the accessible parameter `y`. Hagopian's `⟨p₁, p₅⟩` is at
  `[3/22, 19/22]` with `π[k⁻¹(i/22)] = (i, 0)`; using T6 there needs `y ∉ [3/22, 19/22]`, i.e. the
  reparametrization of `k` by a homeomorphism of `[0, 1]` moving `y` (commission 163, item D). The
  reparametrization itself (transport of `IsMinimalAdmissible`, `γ`, the collar) is not formalized;
  it is needed only when T6 is used in the proof of Theorem 1.
* **T3 at the end layers.** "each point of `π[E]` is an end point of an arc segment … below `π[E]`"
  is given by Lemma 9 / T6 for the interior parameters `0 < t < 1` only (`no_M_below` needs
  `0 < a`, `b < 1`). The end points `γ 0`, `γ 1` are not covered; Theorem 1 uses only `⟨p₁, p₅⟩`.
* T8, T9 in full, T11, Property 3: as in batch 162 (they wait on `D`, i.e. on T7).

---

## Batch 162: Hagopian 1976 VII, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76G.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 162, …)` in that file; none is a declaration, so the main build has no
`sorry` and `axioms.txt` has no `sorryAx`. **Closed in batch 162:** item A in full —
`halfray_dense` (skeleton shape), `halfray_inter` (new: the two half-rays meet only in the layer) and
**Lemma 7** (`hagopian76_lemma7`, skeleton shape; this closes batch-161 item 7, batch-160 item B and
batch-159 item B). Also closed: T10, Property 2 (`hagopian76_property2`, from Lemma 7). Report:
`doc/batches/REPORT-batch162.md`.

* **B. `hagopian76_lemma9`** (collar form; gives T3 and T6). *Obstruction:* the plane construction of
  p. 345 in the configuration of report 161 §1.6 is not formalized: (1) the chain `{G₁, G₂, G₃}` of
  collar rectangles about `π[E]` with `π[I − {y}]` vertical (inputs available: `exists_collar`,
  `plane_schoenflies₂`, `layer_nbhd_small`); (2) the lift of the chain to `M` and a Lemma-8
  refinement whose links are again rectangles in the quotient (`lemma8_caps_sep` refines `G₂` to
  `C ∩ G₂`, whose image is not a rectangle; the exit point `b₁` of `πh[D]` is on the right side of
  `π[G₂]` only for rectangles); (3) `moore62_theorem28` for the simple domain `π[G₂]`, the interlaced
  points `a₁, b₂, a₂, b₁`, and the continua `πh[D] ∪ (segment of π[A] below πh(u))` and
  `π[C ∪ I] ∪ π[Cl G₁]`.
* **T6.** *Obstruction:* "It follows from the proof of Lemma 9 that there exists a horizontal interval
  `I₁` …" needs the proof of Lemma 9 (item B). Shape proposed in the comment.
* **T7.** *Obstruction:* "By choosing `y` sufficiently close to `E` and `h` sufficiently close to the
  identity, we get that every point of `R²` between `⟨p₁, p₅⟩` and a subarc of `π[A]` … belongs to
  `π[St L]`" is unargued (ledger check 162.4). It needs an accessible point of `M ∩ L₆` above `π[E]`
  (the side needs the collar), Property 1 at it (proved), and control of the links of `L` in collar
  coordinates, as in item B.
* **T8, T9 in full.** *Obstruction:* need `I₂` (T7). Given `I₂`, `D` comes from the Jordan curve
  theorem; property (D) of `hagopian76_T9` follows from "every point between `I₂` and `⟨p₁, p₅⟩` is
  in `π[St L]`" and the position of the verticals; then `hagopian76_T9` gives the first sentence of
  T9. "`L − {L₁, L₁₁}` follows `Cl B`" needs that `Cl B` reaches both verticals.
* **T11.** *Obstruction:* needs `D` (T8); the sides of `K` (batch 161) are decided by abscissae only
  once the links are controlled in collar coordinates.
* **Property 3.** *Obstruction:* needs `D` (T8). (i) "the first point `v`" is unargued (ledger check
  162.7): the set of such `v` is closed only under a crossing property of `D` for limits of crossing
  components; (ii) unchanged from batch 161. The step "By Lemmas 2 and 3" is proved
  (`hagopian76_property3_shift`).

**Not needed:** `Lemma7F` (`H76Lemma7.lean`), the existence of `F` for arbitrary `u ≠ t` in one
composant of `Cl R(E)`. It is stronger than what Lemma 7 uses and is probably false in general
(commission 162 §1: near the end of a ray-like composant every continuum through `u` that reaches far
away passes through `t`); it is neither proved nor refuted, and no result depends on it.

---

## Batch 161: Hagopian 1976 VI, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76F.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 161, …)` in that file; none is a declaration, so the main build has no
`sorry` and `axioms.txt` has no `sorryAx`. **Closed in batch 161:** T4 (`hagopian76_eps1`, with the
families recorded in `IsEps1`), ledger check 2 (`hagopian76_eps1_chain`), T5 (`exists_Gset`,
`hagopian76_chain11`, `hagopian76_property1`: the chain `{Gᵢ}`, the refinement `L` and Property 1).
**Partly closed:** T9 (`hagopian76_T9`: first sentence for any `D` with property (D)), Property 3
(`hagopian76_property3_shift`: the step "By Lemmas 2 and 3"), Lemma 7 (`hagopian76_lemma7_triod`,
`hagopian76_lemma7_of_F`: the triod, and the reduction to `u`, `t` in one composant). Report:
`doc/batches/REPORT-batch161.md`.

* **T9, remainder.** `Cl B ⊆ h[E]` and `h⁻¹[Cl B] ⊆ E` a continuum are proved for any open `O` with
  (D) every point of `M ∩ Cl O` in `L₂ ∪ … ∪ L₁₀`; essential to `R(E)` is proved when `Cl B` meets
  links `Lₐ`, `L_c` with `c ≥ a + 3`. *Obstruction:* (D) for `O = π⁻¹[D]`, that `Cl B` reaches far
  apart links, and "`L − {L₁, L₁₁}` follows `Cl B`" all need `D` (T6–T8) in collar coordinates,
  which is not formalized (Lemma 9 and its proof are prerequisites of T6, T7).
* **T11, `hagopian76_T11`.** *Obstruction:* "Note that `K` separates `L₂ ∩ M ∩ π⁻¹[D]` from
  `L₁₀ ∩ M ∩ π⁻¹[D]` in `π⁻¹[D]`" needs `D` (T8) and the cross-cut `K`; and, beyond the cross-cut
  theorem (`plane_split`), that `L₂ ∩ π⁻¹[D]` and `L₁₀ ∩ π⁻¹[D]` lie on opposite sides of `K`. The
  printed family `ρ(A₃, B₃) ≥ 3ε₁` keeps `G₂`, `G₁₀` off `A₃ ⊇ K` but does not decide the side: the
  sets `Gₓ` are not connected and `π` gives no metric control.
* **Property 3, `hagopian76_property3`.** The step "By Lemmas 2 and 3" is proved
  (`hagopian76_property3_shift`), and "By Lemma 1 and Property 1, `L` follows a type A′ continuum
  in `d⁻¹(v)` …" is the first sentence of T9. *Obstruction:* (i) the least `v` ("Let `v` be the first
  point of `[0, 1]` such that …"): no closedness argument is given; (ii) that `d⁻¹(u) = g[d⁻¹(v)]`
  again contains a component of `F ∩ π⁻¹[D]` whose closure meets both verticals — a crossing property
  of `D` in collar coordinates (presumably what the families `ρ(Aᵢ, Bᵢ)`, `ρ(E, π⁻¹(qᵢ))` of `ε₁`
  are for), not argued.
* **6. `hagopian76_lemma9`** (collar form). *Obstruction:* unchanged from batch 160, item E (the chain
  `{G₁, G₂, G₃}` of collar rectangles, Lemma 8 for it, and Theorem 28 for the rectangle `π[G₂]`). The
  configuration of report 160 §1.E was checked against the text (report 161 §1.6): the interlacing
  `a₁, b₂, a₂, b₁` is right, but the second continuum must be `πh[D]` *together with the segment of
  `A` below `πh(u)`* (otherwise it does not reach the bottom side at `b₂`), and the exit point `b₁`
  of `πh[D]` lies in `Cl π[L₃]`, which is on the right side only if the links are collar rectangles.
* **7. `hagopian76_lemma7`** (*closed in batch 162*, `Hagopian76G.lean`, by half-ray density). The triod is proved, and Lemma 7 follows from the existence of `F`
  (`hagopian76_lemma7_of_F`), proved when `u` and `t` lie in different composants of `Cl R(E)`.
  *Obstruction:* `u`, `t` in one composant of `Cl R(E)`. By the triod lemma, a continuum through
  `uⱼ` that is not inside `Hⱼ` contains all of `Tⱼ` or all of `Vⱼ`; so `F` cannot be taken near the
  `Hⱼ` (as Hagopian's "essential to `fhᵢ[R(E)]`" may suggest), and the argument must use that `u`,
  `t` are limits.
  **Property 2** (T10), the only use of Lemma 7 on p. 346, is used twice on p. 348 ("for otherwise, a
  subcontinuum of `L` would violate Property 2"), each time only to get a point of `H` within `ε₂`
  of `π⁻¹(p₄)`; no other route to it was found.

---

## Batch 160: Hagopian 1976 V, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76E.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 160, item …)` in that file; none is a declaration, so the main build has
no `sorry` and `axioms.txt` has no `sorryAx`. **Closed in batch 160:** batch-159 item A in full —
`hagopian76_lemma6_X`, `hagopian76_closure_extUnion`, `hagopian76_lemma6`,
`hagopian76_Rset_composant`, `hagopian76_essential_typeA'` — and the two inputs to Lemma 9 named in
batch 159, item E (1)–(2): `plane_schoenflies₂` (Schoenflies with two adjacent sides prescribed) and
`layer_nbhd_small` (upper semicontinuity in metric form). Report: `doc/batches/REPORT-batch160.md`.

* **B. `hagopian76_lemma7`.** Lemma 6 is no longer an obstruction. *Obstruction:* (1) "By Lemma 2, an
  integer `i` and a homeomorphism `f` of `M` onto `M` exist such that a continuum `F` essential to
  `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects `A`": `u`, `t` are limit points of the
  `uᵢ ∈ Uᵢ`, `tᵢ ∈ Tᵢ` in `Cl R(E)` and `A` is the `ε/4`-ball about the limit `p` of the `pᵢ`; Lemma 2
  moves one point at a time, and the existence of a continuum essential to a translate of `R(E)`
  through `u`, missing `t` and meeting `A` is not argued (the composant property of `R(E)`, now
  proved, gives continua in `R(E)` joining points of `R(E)`, but not through the limit points with
  the separation from `t`); (2) "Note that `g[F] ∪ Hⱼ` is a triod in `M`": the three arms (`g[F]`
  from `uⱼ` towards `A`, which `Hⱼ` misses, and the two parts of the type A′ continuum `Hⱼ` from `uⱼ`
  to `Tⱼ` and to `Vⱼ`) and the fact that `g[F]` misses `tⱼ`, `vⱼ` but not the whole of the end sets
  are not written out.
* **E. `hagopian76_lemma9`** (collar form). (1) and (2) of batch 159 are now proved
  (`plane_schoenflies₂`, `layer_nbhd_small`). *Obstruction:* (3) the chain `{G₁, G₂, G₃}` built from
  collar rectangles with the four `ε` conditions, Lemma 8 applied to it, and the application of
  Theorem 28 (configuration as reconstructed in report 159 §1.E: the rectangle `π[G₂]` as the simple
  domain, continua `π[C ∪ I]` and `πh[D]`, four boundary points in interlaced order) — not
  formalized.

---

## Batch 159: Hagopian 1976 IV, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76D.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 159)` in that file; none is a declaration, so the main build has no
`sorry` and `axioms.txt` has no `sorryAx`. **Closed in batch 159:** the plane Schoenflies theorem
with one side prescribed (`plane_schoenflies`), the two-sided collar of an arc (`exists_collar`),
and Lemma 8 with prescribed caps (`hagopian76_lemma8_caps`, shape chosen). The batch-158 items B
(two-sided extension, not needed), C, D, F remain open as below (C, D unchanged; F restated in collar
form). Report: `doc/batches/REPORT-batch159.md`.

* **A. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
  `hagopian76_essential_typeA'`.** *Closed in batch 160.* Not formalized in batch 159. *Obstruction (step 5 of Lemma 6):* (a) the
  exhausting sequence `{Fᵢ}` with `R(X, E) = ⋃ Fᵢ` ("Since M is second countable, …"): the
  extensions are linearly ordered by inclusion (item A of batch 158 makes `E` an initial segment of
  each; that of two extensions one contains the other is not proved in the repository, as far as
  checked), and a countable
  cofinal subfamily needs that comparison; (b) the limit `c` of the far ends `zᵢ` and
  `c ∈ Cl R(X, E) − R(X, E)`, which uses an extension `L ⊇ K ∪ {c}` (again the linear order) and a
  `δ`-homeomorphism `f` with `f(c) = zᵢ` (Lemma 2, available); (c) the two one-sentence triod
  arguments for `L ∩ f[L] = ∅` and `f[L] ⊆ R(X, E)`. Steps 6–8 need, in addition, the triods
  `C ∪ N ∪ h₁⁻¹[N] ∪ h₂⁻¹[P]` and that of [5, Theorem 1, ¶2]. `hagopian76_essential_typeA'` needs the
  containment of an essential continuum in one extension (from (b)); the rest is
  `isTypeA'_of_subcontinuum` with Lemma 5.
* **B. `hagopian76_lemma7`.** *Obstruction:* item A (Lemma 6).
* **E. `hagopian76_lemma9`** (collar form, `DecompAccessibleC`). Proved around it: the collar
  (`exists_collar`), Schoenflies (`plane_schoenflies`), Lemma 8 with caps, Theorem 28. *Obstruction:*
  (1) coordinates in which `π[I − {y}]` is vertical in the same collar as `π[E]`: the collar does not
  prescribe a second arc; what is needed is Schoenflies with two adjacent sides prescribed (Moore's
  `m19_schoenflies_boundary_proof` prescribes all four, so the transport is the same as for
  `plane_schoenflies`, with the quadrilateral cut so that `π[I]`, `π[E]` are two sides), applied to the
  simple closed curve formed by a sub-arc of `π[E]`, `π[I]` and a closing arc; (2) the chain
  `{G₁, G₂, G₃}` with `π[Gᵢ]`, `π[Gᵢ] ∩ π[Gᵢ₊₁]` open disks (rectangles in collar coordinates pulled
  back by `π`; needs `π⁻¹` of a small rectangle about a third of `π[E]` to lie within `ε` of `Hᵢ`,
  i.e. upper semicontinuity in metric form); (3) the configuration for Theorem 28 (report 159 §1.E:
  the domain `π[L₂]`, which after Lemma 8 is `π[C ∩ G₂]` and need not be a disk — Lemma 8 with caps
  should be applied with `C` replaced by a saturated set whose image is a disk, or Theorem 28 applied
  to the rectangle `π[G₂]` with the freeness of `L` used separately).

---

## Batch 158: Hagopian 1976 III, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76C.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 158)` in that file; none is a declaration, so the main build has no
`sorry` and `axioms.txt` has no `sorryAx`. **Closed in batch 158:** items A (D1:
`hagopian76_lemma4_layers`, `hagopian76_no_swallowed_layer`, in the strong form
`hagopian76_initial_segment`) and B (`hagopian76_lemma5`) of the batch-157 section below; their
commented-out copies in `Hagopian76A.lean` / `Hagopian76B.lean` are replaced by pointers. Report:
`doc/batches/REPORT-batch158.md`.

* **B. `hagopian76_two_sided_extension`.** *Not needed:* Lemma 5 is proved with one extension on
  each side. *Obstruction:* item A makes `E` an initial segment of each extension, but the union
  `F₁ ∪ F₂` needs a glued admissible map, its irreducibility between far points, and `F₁ ∩ F₂ = E`
  (the tail of `F₁` beyond `Z` disjoint from the tail of `F₂` beyond `X`): an atriodicity argument of
  the type of `ext_of_branch`, not formalized.
* **C. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
  `hagopian76_essential_typeA'`.** The D1 obstruction is removed (step 6's "subcollection" is item A,
  Lemma 5 is proved). *Obstruction:* steps 1–8 of Lemma 6 (report 157 §1.C, report 158 §1.C) were not
  formalized; the main work is step 5 (`c ∉ R(X, E)` for a limit `c` of the far ends `zᵢ` of the
  `Fᵢ`, via a `δ`-homeomorphism `f` with `f(c) = zᵢ` and `f[L] ∩ L = ∅`) and the triods of steps 7 and 8.
  `hagopian76_essential_typeA'` also needs the containment of an essential continuum in one extension,
  which follows from step 5 (report 158 §1.C); the type A′ structure of a subcontinuum of an
  extension meeting two layers is proved (`isTypeA'_of_subcontinuum`, `HPC/Hagopian/H76Sub.lean`). `hagopian76_Rset_composant`
  uses Lemma 6.
* **D. `hagopian76_lemma7`.** Lemma 5 is proved; Lemma 6 (the limit points in `Cl R(E)`, the
  essential continuum through `u`) is open. *Obstruction:* item C.
* **F. `hagopian76_lemma9`.** Proved around it: `exists_quotient_plane'` (the arc `γ`),
  `moore62_theorem28` (the cited plane theorem). *Obstruction:* (1) the straightening of the arc
  `π[E]` by a homeomorphism of the plane, which `AbutSameSide` builds into the conclusion, is not
  available for the plane in the repository (Moore 1919's `m19_schoenflies` is stated for his
  abstract spaces and simple closed curves); (2) the three-link chain `G` with `π[Gᵢ]`,
  `π[Gᵢ] ∩ π[Gᵢ₊₁]` open disks, and Lemma 8 with prescribed caps. *Plan* in report 158 §1.F: prove arc
  straightening from the Jordan curve theorem and accessibility, or replace `AbutSameSide` by a
  side-of-a-simple-closed-curve form.

---

## Batch 157: Hagopian 1976 §2 continued, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76B.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 157)` in that file; none is a declaration, so the main build has no
`sorry` and `axioms.txt` has no `sorryAx`. They supersede items D1, E, F, G of the batch-156 section
below (whose commented-out copies remain in `Hagopian76A.lean`, except D1, now a pointer). The
standing remark of the batch-156 section applies. Report: `doc/batches/REPORT-batch157.md`.

* **A. D1: `hagopian76_lemma4_layers` (re-rendered) and `hagopian76_no_swallowed_layer`.**
  *Proved:* the two are equivalent without homogeneity
  (`hagopian76_lemma4_layers_of_no_swallowed`, `hagopian76_no_swallowed_of_lemma4_layers`). The
  step supplied is that `k⁻¹(1) ⊆ d⁻¹(s)` (otherwise `k⁻¹(1) = d⁻¹(u)`, `u < s`, and `d⁻¹[[0, u]]` is a
  proper subcontinuum of `E` meeting both end sets). So D1 is exactly the exclusion of the swallowed
  configuration `d⁻¹(s) ∩ E = k⁻¹[[t₀, 1]]`, `t₀ < 1`.
  *Obstruction:* the half-bar model (batch-156 section, D1) realizes the configuration without
  homogeneity, so homogeneity must enter. The commission's route was followed: for `x ∈ k⁻¹(c)`,
  `t₀ < c < 1`, points of `d⁻¹((s, 1])` accumulate at `x` (the layer `d⁻¹(s)` has void interior in
  `F` while `k⁻¹((t₀, 1))` is open in `E`), Lemma 2 gives small `h` with `h(x) ∈ d⁻¹(u)`, `u > s`, and
  Lemma 3 gives `h[k⁻¹(c′)] = d⁻¹(u(c′))` for `c′` near `c` whenever `d⁻¹(u)` misses `h[X ∪ Z]`. This
  only says that `F` near `d⁻¹((s, s + η))` is a homeomorphic copy of `E` near `k⁻¹(c)`; no
  contradiction with atriodicity or with the irreducibility of `F` between `d⁻¹(s)` and `d⁻¹(1)` was
  found. What is missing: an argument that excludes a nowhere dense layer of `F` containing a set
  with interior in `E`, using the homogeneity of `M` beyond Lemmas 2 and 3 (for instance, a
  comparison of `F` with `h[F]` for `h` moving a point of `k⁻¹((t₀, 1))` into `F ∖ E`, where the three
  continua `E`, `d⁻¹[[s, 1]]`, `h[E]` meet; no triod was obtained).
* **B. `hagopian76_lemma5`; `hagopian76_two_sided_extension`.**
  *Proved:* upper semicontinuity (`hagopian76_lemma5_usc`), lower semicontinuity at every layer
  other than the end sets (`hagopian76_lemma5_interior`, by Lemmas 2 and 3 with `F := E`, without
  D1), and the reduction of Lemma 5 to the end sets (`hagopian76_lemma5_of_ends`).
  *Obstruction at the end sets:* Hagopian's route applies Lemma 3 to `U ⊇ X` in his two-sided `F`
  and needs the layers `Yᵢ` of `E` near `X` to be layers of `F` (condition (2), "`Yᵢ ∈ B`"); by
  `lemma4_layers_aux` applied to an extension away from `Z`, this holds unless the layers of `E` near
  `X` are swallowed by the layer of that extension containing `X`: D1 at `X`. Lemma 3 with `F := E`
  is not available at `X` (its hypothesis `h[Y] ∩ (X ∪ Z) = ∅` fails for `Y = X` and `h` near the
  identity).
  *Obstruction for the two-sided extension:* not formalized. With extensions `F₁` away from `X` and
  `F₂` away from `Z` (Lemma 4) and tails `C₁ = d₁⁻¹[[s₁, 1]]`, `C₂ = d₂⁻¹[[s₂, 1]]`, the natural argument
  (irreducibility of `F₁ ∪ F₂` between far points, then Kuratowski's criterion and the 1975 ¶2
  argument, as in `ext_of_branch`) needs `C₁ ∩ E = Z` and `C₂ ∩ E = X`, so that `F₁ ∩ F₂ = E`. That is
  D1 for `F₁` at `Z` and for `F₂` at `X`. Without it `C₁ ∩ E = k⁻¹[[t₁, 1]]`, `C₂ ∩ E = k⁻¹[[0, t₂]]`, and
  when `t₁ ≤ t₂` the tails overlap inside `E` in `k⁻¹[[t₁, t₂]]` (a set with interior in `E` if
  `t₁ < t₂`); no type A′ structure on `F₁ ∪ F₂` with end sets missing `E` was found in that case.
* **C. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
  `hagopian76_essential_typeA'`.** Steps 1–8 of Lemma 6 are checked in the report (§1.C). Steps 1–5,
  7 and 8 use Lemmas 1, 2, 4 and irreducibility only. Step 6 ("no element `Y` of the decomposition of
  `N` has the property that `h₁⁻¹[Y]` contains `N`") uses the p. 342 remark that the decomposition of
  `N` has that of `K` as a subcollection: D1 (the `ε₁` of step 6 is chosen for the layers of `K`, and a
  layer of `N` swallowing layers of `K` is not controlled by it). The claim "every continuum
  essential to `R(E)` is of type A′" needs (i) the continuum to lie in one extension (not argued; `R(X,
  E)` is an increasing union of closed sets) and (ii) lower semicontinuity of the extension's
  decomposition at the layers it meets, including possibly its end sets (item B). "`R(E)` is a
  composant of `Cl R(E)`" uses Lemma 6. *Obstruction:* items A and B.
* **D. `hagopian76_lemma7`.** Uses Lemma 5 (the decompositions of the essential continua `Hᵢ`, `F`) and
  Lemma 6 (the limit points in `Cl R(E)`; `F` essential to `fhᵢ[R(E)]` containing `u`). *Obstruction:*
  items B and C.

---

## Batch 156: Hagopian 1976 §2, items left open (commented out, never `sorry`)

These skeleton statements of `HPC/Hagopian/Hagopian76A.lean` are **open**. Each is kept as a block
comment headed `OPEN (batch 156)` in that file. None is a declaration, so the main build still has
no `sorry` and `axioms.txt` has no `sorryAx`. Everything else in batch 156 is proved
(`doc/batches/REPORT-batch156.md`).

**Standing remark.** All these statements assume a homogeneous indecomposable plane continuum `M`
with a type A′ subcontinuum `E`. By Theorem 1 of Hagopian 1976 (still to be proved; batches 157–)
no such `E` exists, so none of the statements can be refuted inside such an `M`. The obstructions
below are gaps in the printed arguments, not counterexamples.

* **D1. `hagopian76_lemma4_layers`** (p. 341, first paragraph of the proof of Lemma 4: "There exists
  a positive number `s` such that `d[E] = [0, s]`. … Since the decompositions of `E` and `F` are
  minimal, each element of the decomposition of `E` (except possibly `k⁻¹(1)`) is an element of the
  decomposition of `F`.").
  *Proved instead:* `hagopian76_lemma4_layers'`. It gives `d⁻¹[0, s) ⊆ E ⊆ d⁻¹[0, s]`, every layer of
  `E` lies in a layer of `F`, and a layer of `E` lying in `d⁻¹(u)` with `u < s` equals `d⁻¹(u)`.
  *Obstruction:* minimality alone does not give `E = d⁻¹[0, s]`, nor "every `k⁻¹(t)` with `t ≠ 1` is
  a `d`-layer". The failures can only occur at the layer `d⁻¹(s)`. Here is a plane configuration,
  without homogeneity, with all the other hypotheses. Let `F` be the union of a ray from `X` that
  oscillates onto the lower half `[−1, 0]` of a vertical bar `β = {0} × [−1, 1]`, the bar `β`, and a
  second ray from the right that oscillates onto all of `β`. `F` is of type A′, and `β` is one
  layer `d⁻¹(s)`. Now take `E` = (first ray) ∪ `β`. Its minimal decomposition has the lower half of
  `β` as one layer `k⁻¹(t₀)`, `t₀ < 1`, and the remaining points of `β` as layers. So
  `k⁻¹(t₀) ⊊ d⁻¹(s)`. With the same `F`, `E′` = (first ray) ∪ (lower half of `β`) is of type A′. It is
  irreducible from `X` to any point of the half-bar, which is its end layer. Then `d[E′] = [0, s]`,
  but `d⁻¹(s) = β ⊄ E′`, so `E′ ≠ d⁻¹[0, s]`. Closing the gap needs an argument that uses the homogeneity of `M`. Lemma 4's
  main proof does not use this paragraph (`hagopian76_lemma4_chain` is proved without it). Lemma 5
  uses the two-sided analogue (item E).
* **D2. `hagopian76_lemma4`, second half; `hagopian76_lemma4_seq`** (p. 341: "Since `F` is
  irreducible between `X` and `d⁻¹(1)`, it is a proper subset of an element of `𝓕` that is
  contained in `F ∪ h⁻¹[F]` (Lemma 1).").
  *Proved:* the linear order (`hagopian76_lemma4_chain`). The sequence form, given no maximal element
  (`hagopian76_lemma4_seq_of_noMax`, via `exists_strictMono_seq_of_chain`), is also proved.
  *Proved since (continuation of batch 156):* the second half of the step. If a continuum `F″`
  satisfies `∅ ≠ F″ ∩ F ⊆ d⁻¹(1)` and `F″ ⊄ F`, then `F` has a proper extension away from `X`
  (`HPC.Hagopian.ext_of_branch`, `HPC/Hagopian/H76Lemma4Ext.lean`). The extension is a continuum `H` in
  `F ∪ F″` irreducible between a point of `X` and a point of `F″ ∖ F`. It contains `F`, it is of
  type A′ by Kuratowski's criterion (`hagopian75_lemma2`) and the 1975 ¶2 argument, and its end layer
  at `X` is exactly `X`. So Lemma 4 and its countable form hold as printed whenever every extension
  has such an `F″` (`hagopian76_lemma4_of_branch`, `hagopian76_lemma4_seq_of_branch`, in
  `Hagopian76A.lean`).
  *Closed (continuation of batch 156):* the existence of the extension, unconditionally.
  `HPC.Hagopian.exists_proper_extension` (`HPC/Hagopian/H76NoMax.lean`) shows that in a compact,
  homogeneous, hereditarily unicoherent, atriodic space every continuum with a minimal admissible map
  `d` has a proper extension with the same end layer `d⁻¹(0)`. The proof follows Hagopian's set-up
  (`p ∈ d⁻¹(1)`, an `ε`-homeomorphism `h` with `h(p) = q ∈ d⁻¹((1/2, 1))`, `B = h⁻¹[F]`) and supplies
  the missing step by a case analysis: `F ⊆ B` (`ext_of_subset`); a half of `B` meeting `F` only in
  `d⁻¹(1)` (`ext_of_branch`); and the configuration above (a layer of `B` containing a tail of `F`),
  which is handled by the three-continua argument (`three_continua`, `ext_of_side`,
  `H76NoMaxBasic.lean`, `H76NoMaxCases.lean`). So `hagopian76_lemma4` and `hagopian76_lemma4_seq`
  are proved as printed (`Hagopian76A.lean`; standard axioms only).
* **E. `hagopian76_lemma5`** (p. 341: "There exists a type A′ continuum `F` in `R(E)` that is the
  union of two extensions of `E` such that the end sets `T` and `V` of `F` miss `E` (Lemma 4). …
  In fact, each element of `A` that is not an end set of `E` is an element of `B`.").
  *Obstruction:* Lemma 4's "no maximal element" (D2) is now proved, so it no longer blocks. The claim "each
  element of `A` that is not an end set of `E` is an element of `B`" is the two-sided form of D1.
  For layers of `E` lying strictly inside, it follows by the argument of
  `hagopian76_lemma4_layers'`. The check that the union of an extension away from `X` and one away
  from `Z` is of type A′ is also not written out. The rest of the proof (the choice of `h` with
  (1)–(3) by Lemma 2, then Lemma 3, which is proved) is routine once `F` exists.
* **F. `hagopian76_closure_extUnion`, `hagopian76_lemma6`, `hagopian76_Rset_composant`,
  `hagopian76_essential_typeA'`** (pp. 341–343). Step 4 of Lemma 6 uses the sequence `{Fᵢ}` (D2, now proved).
  The remark "the decomposition of `F` is a continuous collection (Lemma 5)" is used throughout,
  and "every continuum essential to `R(E)` is of type A′ (Lemma 5)" depends on E. "Since `M` is
  atriodic, `R(E)` is a composant of `Cl R(E)`" uses Lemma 6 (indecomposability of `Cl R(E)`).
  *Obstruction:* Lemma 5 (Lemma 4 is proved since the continuation of batch 156). The individual steps 1–3 of Lemma 6 need only
  Lemma 1 and the irreducibility of `E` and its extensions. They were checked but not formalized.
* **G. `hagopian76_lemma7`** (pp. 343–344). It uses Lemma 2, "essential" continua, and their type A′
  decompositions (Lemma 5, so E), on `Cl R(E)`. *Obstruction:* items E and F.

---

## Open items of the main build (`sorry`): none since batch 132

Item 1 (`HPC.Plane.fugate_cor1`) is closed: see the table below. The main build carries no `sorry`
and `sorryAx` occurs in no line of `axioms.txt`. The former text of item 1 is kept at the end of
this file.

---

## Closed in batch 151: Moore 1922, Theorem 4

**`HPC.Jones.moore22_theorem4`** (Moore, *Concerning connectedness im kleinen and a related
property*, Fund. Math. 3 (1922), Theorem 4, p. 235), open in batch 150 (kept as a comment at the end
of `HPC/Jones/Moore22T4.lean`, never `sorry`), is **proved** in batch 151
(`HPC/Jones/Jones49C.lean`, statement verbatim, standard axioms only). The commented copy in
`Moore22T4.lean` is deleted.

The batch-150 obstruction (the sector theorem and the cyclic order of crossing continua) is removed by
`HPC.Jones.sector_theorem` and `HPC.Jones.sector_cyclic_order` (`HPC/Jones/Jones49CStrip.lean`,
`Jones49COrder.lean`, `Jones49CAnn.lean`): crossing continua of a square annulus are lifted to the
strip `r₁ ≤ y ≤ r₂` by the component criterion for a continuous logarithm, and separated there.
* **Sufficiency:** property S gives Whyburn's local condition (pigeonhole,
  `Sector.hloc_of_propertyS`), and `moore22_sufficiency_local` (Moore's p. 236 argument, for any open
  `R` with connected boundary; `HPC/Jones/Jones49CMoore.lean`) gives local connectedness; the
  boundary is connected by batch 150's `isConnected_frontier_of_mooreSimplyConnected`.
* **Necessity:** `Sector.propertyS_of_locallyConnected` (Moore's pp. 236–237 argument with the
  repaired last step: the points used for the final contradiction are taken in `M`, on the middle
  square, inside the pieces cut off by the crossing continua). Simple connectivity is not used.

---

## Closed in batch 150: Whyburn (9.2) and `jones49_some_order_two`

The two skeleton items left open in batch 149 (kept as comments in `HPC/Jones/Jones49A.lean`) are
**proved** in batch 150 (`HPC/Jones/Jones49B.lean`, statements verbatim, standard axioms only); the
commented copies in `Jones49A.lean` are deleted.
* `HPC.Jones.whyburn_9_2`: from `whyburn_9_1` (batch 149) and the separating point-order theorem for
  open sets, `countable_sepPoint_not_hasOrder_two` (`HPC/Jones/Jones49Sep.lean`), applied to each
  set of a countable basis.
* `HPC.Jones.jones49_some_order_two`: from `whyburn_9_2` through
  `jones49_some_order_two_of_whyburn_9_2`.

The obstruction recorded in batch 149 ((8.2), (3.2) with §§1–2, (8.3)) is met by a shorter route:
the separating points of an open set `R` that separate two fixed basic open sets `U`, `W` within a
component are linearly ordered (the order of Whyburn's §1, `SepChain.lt`), all but countably many of
them are two-sided limits in this order with empty "residue", and each of those has arbitrarily small
open neighbourhoods with exactly two frontier points (`HPC/Jones/Jones49Chain.lean`). Neither (8.2),
nor the non-separated cuttings of §2, nor (8.3) is used; (3.2), (8.4) and (8.41) are corollaries.

---

## Closed in batch 142: Moore 1919, Theorem D

`HPC.Moore.m19_theoremD` (p. 173), open since batch 141 (kept as a comment in
`HPC/Moore/M19CD.lean`, never `sorry`), is **proved** in batch 142 (`HPC/Moore/M19DThm.lean`,
collected in `HPC/Moore/M19CD2.lean`; standard axioms only). The comment in `M19CD.lean` is removed.
The three obstructions recorded in batch 141 are met as follows (REPORT-batch142.md):

1. Theorem C is used only in a corrected form, for curves touching `ABCDA` from within nowhere
   (`curve_rulable`, `m19_theoremC_corrected`). Moore's `J̄` is not used: a closed curve `h` about the
   relevant compact set is built so that it crosses `ABCDA` at each common point
   (`exists_nice_curve`, from lenses `lens_data` merged by Theorem 42).
2. The induction runs over the number of curves of a finite subcover (`rulable_of_cover`): a
   subdivision without the interior of `h` is a new quadrilateral covered, with its boundary, by the
   other curves, and receives its own curve `h`. No subdivision boundary has to be compared with `g₂`.
3. `J′` and the annulus of Fig. 2 are not needed.

The region form used in Theorem E is now unconditional (`m19_theoremD_regions`, `M19CD2.lean`).

---

## Closed items

| Former statement | Former item | Closed in | Now proved by |
|---|---|---|---|
| `HPC.Jones.moore22_theorem4` (Moore 1922, Theorem 4; batch-150 item, kept as a comment, never `sorry`) | — | batch 151 | `HPC.Jones.moore22_theorem4`, `HPC/Jones/Jones49C.lean`: sufficiency by `moore22_sufficiency_local` and `Sector.hloc_of_propertyS`, necessity by `Sector.propertyS_of_locallyConnected` (`HPC/Jones/Jones49CMoore.lean`), both through the cyclic order of crossing continua (`sector_cyclic_order`). |
| `HPC.Jones.whyburn_9_2` (Whyburn (9.2); batch-149 item, kept as a comment, never `sorry`) | — | batch 150 | `HPC.Jones.whyburn_9_2`, `HPC/Jones/Jones49B.lean`: `whyburn_9_1` on a countable basis and the separating point-order theorem for open sets (`countable_sepPoint_not_hasOrder_two`, `HPC/Jones/Jones49Sep.lean`). |
| `HPC.Jones.jones49_some_order_two` (batch-149 item, kept as a comment, never `sorry`) | — | batch 150 | `HPC.Jones.jones49_some_order_two`, `HPC/Jones/Jones49B.lean`, from `whyburn_9_2` and `jones49_some_order_two_of_whyburn_9_2`. |
| `HPC.Moore.m19_theoremD` (Moore 1919, Theorem D; batch-141 item, kept as a comment, never `sorry`) | — | batch 142 | `HPC.Moore.m19_theoremD`, `HPC/Moore/M19DThm.lean` (collected in `M19CD2.lean`): induction on a finite subcover; at each step a curve about the uncovered part crossing `ABCDA` at each common point (`exists_nice_curve`) and a ruling missing it by the corrected Theorem C (`curve_rulable`). |
| `HPC.Moore.fa_theorem41` (Moore F.A. 1916, Theorem 41, Case II; batch-139 item, kept as a comment, never `sorry`) | — | batch 140 | `HPC.Moore.fa_theorem41`, `HPC/Moore/M41.lean` (Case II: `fa_theorem41_caseII`). The curve is the boundary of an unbounded component `V` of `S − (I₁' + I₂')`; it is built from `J₂` by replacing a null family of arcs by chords of `J₁` (`Gen.arc_replace`, with Theorem A of 1919 for nullity: `chords_null`). |
| `HPC.Moore.fa_theorem42` (Moore F.A. 1916, Theorem 42; batch-139 item, kept as a comment) | — | batch 140 | `HPC.Moore.fa_theorem42`, `HPC/Moore/M41.lean`, from `fa_theorem42_of_41` and `fa_theorem41`. |
| `HPC.Moore.fa_theorem43` (Moore F.A. 1916, Theorem 43, corrected with `G` nonempty; batch-139 item, kept as a comment) | — | batch 140 | `HPC.Moore.fa_theorem43`, `HPC/Moore/M43.lean`: the intersection analogue of Theorem 41 (`dual_step`, from `dual_component`) iterated over `G` (`iterate_inner`). The printed form stays refuted for `G = ∅` (`not_fa_theorem43_printed`). |
| `HPC.Jones.jones51_theorem1` (Jones 1951, Theorem 1: a homogeneous, hereditarily unicoherent, compact metric continuum is indecomposable; batch-135 skeleton item, kept as a comment, never `sorry`) | — | batch 136 | `HPC.Jones.jones51_theorem1`, `HPC/Jones/Jones51Thm1.lean`, with `[Nontrivial X]` dropped. Proved without the decomposition space: an irreducible continuum between `a` and a point `b` of `aposSet a`, a third class `L_c` inside it, then Jones's step (5); hereditary unicoherence is used on `M` only. Uses the spreading lemma (`aposAt_of_isContinuum_interior`), Bing's Corollary 2 transferred by homogeneity and `jones51_lemma`. The obstruction formerly recorded here (decomposition space, Whyburn 6.21) is also removed: both are proved (`HPC/Jones/Decomp.lean`, `HPC/Jones/Whyburn.lean`). |
| `HPC.Plane.fugate_cor1` (Fugate 1966, Corollary 1, with Fugate's hypothesis) | 1 | batch 132 | `HPC.Plane.fugate_cor1`, `HPC/Plane/Ingram68.lean`; also `HPC.Plane.fugateU_holds`. Proved in batch 132 from Fugate's Theorem 1 and the property (∗) of Ingram 1968 (`fugate_cor1_of_ingramStar`, `HPC/Plane/Fugate66Cor1Proof.lean`). (∗) is proved by the direct route (`ingramStar_holds`, `HPC/Plane/Ingram68Core.lean`, `HPC/Plane/Ingram68Star.lean`): Ingram's Lemmas 1 and 2 with terminality and irreducibility, his appeals to Sorgenfrey replaced by a core lemma, not through his Theorem 2(2) and circle-likeness (Nadler 12.51 is proved, `isSnakeLike_of_subset_circleLike`, but not used). Fugate gives no proof, and Ingram postdates Fugate. |
| `HPC.Description.covering_step` | 2 | batch 114 | `HPC.lehner_lemma3_two` (Lehner's Lemma 3, `n = 2`), `HPC/PseudoArc/Lehner.lean` |
| `HPC.Description.theorem14` | 3 | batch 115 | `HPC.Description.theorem14`, `HPC/PseudoArc/Thm14.lean` |
| `HPC.Plane.geomLemma'_of_two_le_rank` | 4 | batch 113 | `HPC.Plane.geomLemma'_of_two_le_rank`, `HPC/Plane/CubeCycle.lean` |
| Bing 1948, Theorem 4 as printed with at least four coarse links (`Theorem4LiteralGe4`) | 2 | batch 125 | `HPC.Fold.theorem4_literal_ge4`, `HPC.Fold.theorem4LiteralGe4_holds` (`HPC/Plane/Jct1.lean`, proof in `HPC/Fold/Theorem4Ge4.lean`): `two_core` with the pair form of Theorem 3 at both ends; with three coarse links the statement is false (`not_theorem4Literal`, `not_theorem4LiteralND`) |
| Bing 1948, Theorem 3 as printed (only-clause; `Theorem3LiteralOr`, `Theorem3Pair`) | part of 2 | batch 124 | `HPC.Fold.theorem3_literal`, `HPC.Fold.theorem3_pair` (`HPC/Fold/Theorem3Pair.lean`); Theorem 4's only-clauses refuted for `m = 3` (`not_theorem4LiteralND`) |
| `HPC.Fold.theorem3_end` | 1 (numbering of batches 116–122) | batch 123 | `HPC.Fold.theorem3_end` (`HPC/Fold/Theorem4.lean`) from `HPC.Fold.theorem3_bing` (`HPC/Fold/Theorem3Bing.lean`): Bing's Theorem 3 in his two-link form with the end clause, by Bing's induction in the model with three repairs (batch 122) |

Their former consequences are proved with them: `exists_description_covering` (in `Lehner.lean`),
`theorem15` (in `Thm14.lean`), and `dense_pseudoArcs`, `theorem2_HIC`, `theorem2_1951` (in
`CubeCycle.lean`). See REPORT-batch113.md, REPORT-batch114.md and REPORT-batch115.md.

---

## Relative results

None since batch 131: `PlaneFacts` is proved (`planeFacts_holds`); Theorems 6 and 7 of Bing 1951
(Duke) are unconditional (`theorem6_1951`, `theorem7_1951`, `HPC/Plane/Enc2.lean`).

## Closed in batch 133: `treeLike_nonseparating`

`treeLike_nonseparating` (the implication "tree-like ⇒ no subcontinuum separates the plane",
batch 119, item 5; recorded as a comment in `HPC/Plane/Tree7.lean`, not as a `sorry`) is closed.

* **False as stated up to batch 132.** The repository's `IsTreeLike` (batch 117) did not require
  the links of the tree chains to be bounded, and Mathlib's `diam` of an unbounded set is `0`; so
  `{univ}` was a tree chain of every mesh and every continuum, a circle included, was "tree-like"
  (`HPC.Plane.isTreeLikeOld_of_isContinuum`, with the old definition kept as `IsTreeLikeOld`,
  `HPC/Plane/TreeLikeNS.lean`). A circle separates the plane.
* **Proved under the repaired definition** (`IsTreeLike` now asks `Bornology.IsBounded A`):
  `HPC.Plane.treeLike_nonseparating`, `HPC/Plane/TreeLikeNS.lean`, by a logarithm of `z − p` on a
  fine tree cover and the crossing parity of batch 125 (no Borsuk, no Brouwer). Corollaries: Bing's
  Duke Theorem 7 as printed (`theorem7_1951_treeLike`) and Theorem 6 with its converse
  (`isTreeLike_iff_nonseparating`).

## Batch-132 skeleton items not formalized

Commented out, verbatim, at the end of `HPC/Plane/Ingram68.lean` (not in the build, not `sorry`);
none is needed for (∗) or `fugate_cor1`:

* Sorgenfrey 1944, Theorem 1.8 (`exists_isTriod_of_isWeakTriod`, `not_three_of_isAtriodic`) —
  open; not refuted (the θ-curve of `LEDGER.md`, a weak triod that is not itself a triod,
  does contain a triod, consistent with the claim). The
  repository's core lemma (`isTriod_of_core`) needs one continuum containing the three pairwise
  intersections and none of the three continua; for a general weak triod, which need not be
  unicoherent, no such continuum is available, and the ball constructions of the textbook proof
  were not formalized.
* Ingram, Lemma 3 (`ingram_lemma3`) — open. The subcase where both components `L₁`, `L₂` of
  `H ∩ A` leave `K` is a triod with core `K`; the subcase `L₂ ⊆ K` needs a triod in `K ∪ H`,
  where `K ∩ H` is disconnected (Sorgenfrey's theorem in a non-unicoherent configuration).
* Ingram, Theorem 1 (`ingram_theorem1`) and Theorem 2(2), sufficiency
  (`ingram_theorem2_circleLike`) — not attempted; replaced by the direct route (COMMISSION-batch132.md
  §2, "Alternative route").

## Former text of item 1 (closed in batch 132)

### `HPC.Plane.fugate_cor1` — Fugate 1966, Corollary 1, with Fugate's hypothesis

* **File:** `HPC/Plane/Fugate66.lean`.
* **Statement.** For a finite chain `A 0, …, A k` of snake-like continua, consecutive ones meeting:
  the union is snake-like iff it is atriodic and unicoherent.
* **Depends on it:** nothing in the main build.
* **Known.** Necessity is proved (`fugate_cor1_necessity`). Sufficiency is proved under the stronger
  hypothesis that the union is *hereditarily* unicoherent (`fugate_cor1'`, `fugate_cor1_iff`,
  `HPC/Plane/Fugate66B.lean`). With Fugate's hypothesis the two-piece reduction
  (`hu_union_of_snakeLike`) needs each partial union `A 0 ∪ … ∪ A i` to meet `A (i+1)` in a
  connected set, which unicoherence of the whole union does not obviously give (REPORT-batch101.md,
  item 5). Not class B: the two statements differ in that hypothesis (checked by elaboration in
  batch 103).
* **Batch 124.** Fugate gives no proof; the induction he presumably intends needs condition (U)
  (every partial union unicoherent; equivalently the union hereditarily unicoherent), recorded as
  the open `Prop` `HPC.Plane.FugateU` in `HPC/Plane/Fugate66Cor1.lean`. (U) is *equivalent* to the
  sufficiency half of the corollary (`fugateU_iff_cor1Sufficiency`), and the corollary follows from
  it (`fugate_cor1_of_fugateU`). (U) is neither proved nor refuted; the obstruction (a least
  non-unicoherent partial union, and what a counterexample would have to look like) is in
  REPORT-batch124, Q4.
