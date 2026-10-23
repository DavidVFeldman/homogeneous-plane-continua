# Commission: batch 145 — Part E, Moore 1925 I: the space of elements, Theorems 1–4

**Go!** This batch runs on top of the batch-144 delivery. Four files come with it, as separate
uploads:

* `COMMISSION-batch145.md`: this text, also pasted into the prompt.
* `Moore1925I.lean`: the skeleton.
  * Save it as `HPC/Moore/M25A.lean`. You may split it.
  * Add `import HPC.Moore.M25A` at the end of `HPC.lean`.
  * Adjust its imports to whatever provides `Pt`, `SeparatesPlane`, `SeparatesPts`,
    `planeFacts_holds` and `polyInterior`.
* `moore1925.pdf`: R. L. Moore, *Concerning upper semi-continuous collections of continua*,
  Trans. AMS 27 (1925), 416–428. Save it to `doc/sources/moore1925.pdf`.
* `moore1925-primeparts.pdf`: R. L. Moore, *Concerning the prime parts of a continuum*, Math. Z. 22
  (1925), 307–315. This is the paper of the "methods largely analogous" on p. 420. Save it to
  `doc/sources/`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Moore 1925 §I, Theorems 1–4 (batch 145)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 144

Audited and accepted. The skeleton copy is byte-identical. The statements of
`m19_schoenflies_boundary`, `m19_plane`, `m19_theoremG` and `m19_final` are verbatim. `m19_annulus`
takes the collar form, and `m19_annulus_square` and `m19_openCurve` are added. Both choices are
accepted. `axioms.txt` has 996 lines, and `sorryAx` appears in none of them.

With `m19_plane`, Moore's characterization of the plane is verified: a space satisfying F.A.'s
Axioms 1–8 is homeomorphic, in its region topology, to `ℝ²`.

Your ledger entries are adopted:
* the nine-cell ruling of Fig. 3, not proved as stated (two cuts and two quadrilaterals take its
  place);
* the open curves `kₘ`, `tₙ`, not needed by our route;
* the p. 178 sentences, supplied by `m19_theoremG` and `m19_final`;
* Σ₁ only.

Your Σ₂ conclusion is accepted. Moore 1925 Theorem 21 goes on from 6′ and 7′ to Axioms 6 and 7, so
`m19_plane` applies as it stands. F.A.'s unproved assertion that Σ₁ and Σ₂ are equivalent is not
needed.

## 1. Where this sits

| batch | content |
|---|---|
| 144 | end of Moore 1919: `m19_plane` (done) |
| **145 (this one)** | 1925 §I, Theorems 1–4 and the p. 420 claim: Axioms 1, 2, 4, 5 and F.A. Theorem 4 for the space of elements; the region topology is the quotient topology; two plane facts |
| 146 | Theorems 5–11: arcs of elements, P.C.S. Lemma 8, Moore 1920 Theorem 4, Theorem 11 (the Jordan curve theorem for curves of elements, through Mullikin 1922) |
| 147 | Theorems 12–21 (restricted regions; Axioms 3, 6′, 7′, 6, 7, 8) and Theorem 22 |
| 148– | Jones 1955 Theorem 2, with Jones 1949 |

**Your reading plan's three points**, answered:

1. **Non-compactness.** The batch 136 decomposition results were proved for compact `X`, and `ℝ²` is
   not compact. The skeleton therefore restates them for the plane (`isClosedMap_mk_plane`,
   `quotient_metrizable_plane`). The proofs should go through with compact elements in a proper
   metric space; a general form, if it comes cheap, is welcome.
2. **The Jordan curve theorem in `ℝ²`.** The repository has only the polygonal JCT and polygonal
   Janiszewski (`PlaneFacts`). Moore's §I does not use the JCT for arbitrary plane curves:
   * Theorem 3 uses only *some* enclosing curve, and a polygon (`planeFacts_holds.enclose`) does
     that job;
   * Axiom 8 for the space of elements comes from Theorem 11, the JCT for *curves of elements*,
     which Moore proves from Mullikin's theorem.

   The plane facts this route needs are therefore the compact Janiszewski theorem, Brouwer's
   boundary theorem (both in this batch), and Mullikin's theorem (batch 146). If any of them turns
   out to need the general JCT, say so in the report. The JCT would then be commissioned on its own.
3. **Shortcut.** You suggested verifying Axioms 1–8 directly for the quotient topology, by plane
   topology. It is to be weighed in the batch 146 reading plan, once Theorems 5–11 have been read.
   For this batch, follow Moore.

## 2. Items

Setting and modelling are in the skeleton header. The decomposition is a `Setoid Pt` satisfying
`MooreDecomp`:
* elements compact and connected;
* no element separating the plane;
* Moore's distance form of upper semicontinuity.

The space of elements is the quotient. Moore's notions on sets of elements become quotient-topology
notions once `isLimitElt_iff` is proved.

**A. The quotient.**
* `isClosedMap_mk_plane`: Moore's u.s.c. gives the closed-map property.
* `quotient_metrizable_plane`.
* `isLimitElt_iff`: Moore's limit element is accumulation in the quotient topology.
* `m25_domain_iff`: Moore's domains are the connected open sets.

**B. Theorem 1.** Follow Moore's proof (p. 418), checks 1–2 of §3.

**C. Plane facts.**
* `brouwer_boundary`: the frontier of a component of the complement of a closed connected set is
  connected. This is Brouwer, Math. Ann. 69. Batch 131's `outerComp` material, or the Tree67 files,
  may already contain part of it.
* `janiszewski_compact`: from `janiszewski_polygonal` by approximation, or directly by an
  elementary homology-free proof (Eilenberg's or Kuratowski's). Choose whichever is shorter. Batch 146
  (Theorem 9) and 147 (Theorem 13) also need it.

**D. Theorem 2** (pp. 418–419). The statement is now explicit: complementary domain read as a
component, together with `m25_unbounded_unique`. Moore's proof cites Janiszewski for the step "since
`N̄ + p̄` and `H̄ + p̄` have in common only `p̄`, … either `N̄ + p̄` or `H̄ + p̄` separates `X` from
`Y`". That is `janiszewski_compact` with a connected intersection.

**E. Theorem 3** (pp. 419–420). Moore's proof:
1. a curve `J` enclosing `p` within `e` (PNAS 1925 Theorem 1; use the polygon);
2. `H`, the elements meeting `J`;
3. `D`, the component of `H̄ᶜ` containing `p̄`, and `B = ∂D`;
4. `R`, the elements inside `D`.

Then `R̄ = D` (an element meeting `D` misses `H̄`, so lies in `D`).

**F. Theorem 4.** "Easily established with the help of Theorem 3".

**G. The unnumbered claim of p. 420** (`m25_axioms1245`): Axioms 1, 2, 4, 5 and F.A. Theorem 4
(regions are infinite; nonempty regions, given batch 137's refutation at `R = ∅`) for
`spaceOfElts r`. Then prove `spaceOfElts_topology`.
* Axiom 1 needs a *sequence* of Moore regions forming a basis in Moore's sense. Use Theorem 3 and
  second countability.
* Axiom 4 is Heine–Borel *by Moore regions* for the closure of a region. Note that `σ.cl` and
  `σ.HeineBorel` are defined from `spaceOfElts r`'s regions, not from the quotient topology, so
  `spaceOfElts_topology` (or Theorem 4) is the bridge.
* Read the Math. Z. paper (§§1–2) and record what "methods largely analogous" amounts to.

Once G holds, F.A. Theorems 1–15 hold for the space of elements, by batches 137–138 (Moore's
"consequently Theorems 1–15 of that paper all hold true"). State this as a corollary
(`m25_FA_1_15`) by instantiating the batch 137–138 theorems that use only Axioms 1, 2, 4, 5. Two or
three representative instances suffice, plus a remark in the report listing which F.A. theorems of
1–15 need more than these axioms, if any.

## 3. Places to check (candidate ledger entries)

All are transcribed from page images at 200 dpi.

1. **Theorem 1, I** (p. 418): "Since `p` is closed and bounded the sequence `X₁, X₂, ⋯` contains a
   subsequence of distinct points which has as its sequential limit point some point `X` in `p`."
   The subsequence of *distinct* points need not exist: the `Xₙ` may take finitely many values.
   This is harmless (take a constant subsequence). Record it.
2. **Theorem 1, II:** "Let `p` denote that element of `H₁` which contains `p`". The second `p`
   should be `P`. This is a typographical slip. Record it.
3. **Definition of boundary** (p. 417): "the set of all elements `[x]` of `H` such that `x` either
   belongs to `H` and is a limit element of the set `G—H` or `x` does not belong to `H` but it is a
   limit element of `H`". Read as printed ("of `H`"), the second clause is empty. Read "of `G`".
   Confirm that, so read, it is the quotient frontier.
4. **Definition of complementary domain** (p. 417): "A domain of elements of `G` is said to be a
   complementary domain of a closed set `H` of elements of `G` provided the boundary of `D` is a
   subset of `H`."
   * As printed, `G` itself is a complementary domain of every closed `H`, since its boundary is
     empty.
   * So is the interior of a closed disc of elements, as a complementary domain of the disc.
   * "*The* unbounded complementary domain" (p. 417 and the proof of Theorem 2) is then not unique.

   Record whether Theorem 2 holds under the literal definition. Record also that the skeleton
   reads "component of `Hᶜ`", which is presumably Moore's intent.
5. **Theorem 2's proof:**
   * "`B` is a closed and connected set". Brouwer is not cited here (only in Theorem 3), and `B` is
     the boundary of `Ē` where `E` is a complementary domain of `∂D`, not of `M`. Record what
     supplies the connectedness of `B` (that `(∂D)‾` is connected comes from Brouwer applied to
     `D̄`).
   * "Clearly `Dₓ` contains `D`"; "But `q` does not belong to the boundary of `Dₓ`". Both are
     unargued.
6. **Theorem 3's statement** omits "containing `p`". The skeleton adds `p ∈ R`. Record it.
7. **Theorem 3's proof:**
   * "The point set `H̄` is a continuum" (Theorem 1 gives `H` closed and connected as a set of
     elements; the point form needs the closed map and the connectedness of elements meeting `J`);
   * "It follows that the boundary of `R` is connected";
   * "But clearly `R` is a domain";
   * "the boundary of `R` consists of all those elements `[g]` of `G` such that `g` contains a point
     of `B`".

   All four are unargued. Note too that the last sentence ("every element … is at an upper distance
   less than `e` from `p`") needs `D` to lie inside `J`. This is where the enclosing curve's
   interior is used.
8. **Theorem 4**, "may be easily established with the help of Theorem 3". This is stated without
   proof. Record what the proof uses.
9. **The p. 420 claim** (Axioms 1, 2, 4, 5, F.A. Theorem 4), "by methods largely analogous". This is
   stated without proof. Record it, together with what the Math. Z. paper actually supplies.
10. **The u.s.c. definition** (p. 416) against the open-set form: record the equivalence (with
    compact elements) as proved by `isClosedMap_mk_plane`, and note any use of compactness.

## 4. Deliverables

1. Items A–G.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch145.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 146: 1925 Theorems 5–11, pp. 420–424.

   For the reading plan, the sources are:
   * Moore 1920, *Concerning simple continuous curves*, Trans. AMS 21, p. 342 and Theorem 4;
   * PNAS 10 (1924) (P.C.S.), Lemma 8;
   * Mullikin 1922;
   * F.A. p. 139.

   I will send the first three with the batch 146 commission. For each of Theorems 5–7, 9 and 10
   (proved by analogy only), say what the analogous argument is and whether batches 137–144 already
   contain it for an abstract space satisfying Axioms 1, 2, 4, 5. If they do, the theorem is
   inherited through `m25_FA_1_15`. Weigh your shortcut there.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
