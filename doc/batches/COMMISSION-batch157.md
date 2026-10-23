# Commission: batch 157 — Part E, Hagopian 1976 II: the first paragraph of Lemma 4, Lemmas 5–7, the set-up of Theorem 1

**Go!** This batch runs on top of the batch-156 delivery. Four files come with it, as separate
uploads:

* `COMMISSION-batch157.md`: this text, also pasted into the prompt.
* `Hagopian76B.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76B.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76B` at the end of `HPC.lean`.
* Two sources, for `doc/sources/`:
  * `mazurkiewicz1929.pdf`: S. Mazurkiewicz, *Sur les points accessibles des continus
    indécomposables*, Fund. Math. 14 (1929), 107–115 (scanned two pages to a sheet);
  * `bing1960.pdf`: R. H. Bing, *A simple closed curve is the only homogeneous bounded plane
    continuum that contains an arc*, Canad. J. Math. 12 (1960), 209–230.

  Neither is needed for this batch's items. They are for the reading plan (§4).

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 §2 continued (batch 157)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * `HPC/Hagopian/Hagopian76A.lean`: delete the commented-out copy of each item proved here.
    Replace the commented-out `hagopian76_lemma4_layers` with a one-line pointer to its re-rendering
    in `Hagopian76B.lean`.
* **Root housekeeping (allowed this once).** `REPORT-batch155.md`, `theorems-3-4-scheduling(1).md`
  and `theorems-3-4-scheduling(2).md` are at the root.
  * Delete `REPORT-batch155.md` if it is byte-identical to `doc/batches/REPORT-batch155.md`;
    otherwise move it to `doc/batches/`.
  * Move the two notes files to `doc/notes/`.

## 0. On batch 156

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1339 lines, with `sorryAx` in none. It grew by 53 lines (the main pass and
  the continuation), all on the standard three axioms. The open items are comments, not declarations.
* **Shape changes accepted:**
  * the definitions moved to `H76Defs.lean`;
  * `hu0`, `hu1` dropped in Lemma 3;
  * the `omit` generalizations.

**Accepted.**
* **Lemma 3 as printed.**
* **Lemma 4 in full.** Your continuation supplies Hagopian's "it is a proper subset of an element of
  `𝓕` that is contained in `F ∪ h⁻¹[F]`" by a case analysis, `ext_of_branch` and the three-continua
  argument. The ledger records the step as unargued and true, and it is the longest supplied step so
  far in Part E.
* **The countable form**, by your basic-open-set argument, which is shorter than mine.
* **Lemma 8.**
* **All five consequences of `Hagopian76Thm1`.** Gordh and Jones 1951 are not needed.

**Your standing remark is right and is recorded in the ledger (A.23).** Inside a homogeneous
indecomposable `M` none of §2 can be refuted, because no type A′ `E` exists. Each step must be
proved, or shown not to follow from what its proof uses.

**My error, recorded in ledger C.2.** The batch-156 skeleton rendered "`d[E] = [0, s]`" as
`layerSet d (Icc 0 s) = E`, which also asks `d⁻¹(s) ⊆ E`. Your half-bar model `E′` separates the
two. The printed first two sentences are what `hagopian76_lemma4_layers'` proves. In
`Hagopian76B.lean` the paragraph is re-rendered as printed, so **D1 is now exactly the third
sentence**: every layer of `E` other than `k⁻¹(1)` is a layer of `F`.

## 1. Where this sits

| batch | content |
|---|---|
| **157 (this one)** | D1; Lemmas 5–7 and the two unnumbered claims; the set-up of Theorem 1 (`S`, `π`, the arc `π[E]`, accessibility) |
| 158 | Lemma 9 (decomposable accessibility, Bing 1960 p. 215; Moore 1962 Theorem 28); Property 1 |
| 159– | Theorem 1: Properties 2–4 (Mazurkiewicz 1929 on p. 347) and the induction (Bing 1960 p. 225); `hagopian76_theorem1 : Hagopian76Thm1` |

## 2. Items

**A. D1.** Prove `hagopian76_lemma4_layers` (re-rendered) or `hagopian76_no_swallowed_layer`. By
`hagopian76_lemma4_layers'`, they are equivalent up to bookkeeping; confirm this.
* The configuration to exclude: `d⁻¹(s) ∩ E = k⁻¹[[t₀, 1]]` with `t₀ < 1`. Here `E` has an interval
  of layers, with interior in `E`, inside one nowhere dense layer `W = d⁻¹(s)` of `F`, and the points
  of `F − E` accumulate on `k⁻¹((t₀, 1))` from `d⁻¹((s, 1])`.
* Lemma 3 with `h = id` does not exclude it, because every choice puts an end set inside `W`. I
  checked `E` and its subcontinua `k⁻¹[[a, b]]`; the upper end always lies in `W`.
* Homogeneity has to enter through Lemma 2. One direction to try:
  * take `x ∈ k⁻¹(c)`, `t₀ < c < 1`, and a small `h` with `h(x) ∈ d⁻¹(u)`, `u > s`;
  * then Lemma 3 (with `E`, `Y = k⁻¹(c)`, and `F`, `U = d⁻¹(u)`) gives `h[k⁻¹(c)] = d⁻¹(u)`,
    whenever `d⁻¹(u)` misses `h[X ∪ Z]`;
  * so the layers of `F` just beyond `W` are small-moved copies of layers of `E` inside `W`;
  * look for a contradiction with atriodicity, or with the irreducibility of `F` between `W` and
    `d⁻¹(1)`, as `u ↓ s` and `c` varies.
* If this fails, say exactly what is missing, and do item B anyway.

**B. Lemma 5.**
1. **`hagopian76_lemma5_interior` first.** This is lower semicontinuity at the layers that are not end
   sets, by Lemma 3 with `F := E`. The skeleton docstring has the argument. It does not use D1 or
   Hagopian's `F`. Check it.
2. **`hagopian76_two_sided_extension`.** Hagopian's `F` is the union of an extension away from `X`
   and one away from `Z`, with end sets missing `E`. Is that union of type A′? Use Kuratowski's
   criterion and the 1975 ¶2 argument, as in `ext_of_branch`.
3. **`hagopian76_lemma5`** (the end sets).
   * Hagopian's route puts the end set `X` inside a layer `U` of `F`. It needs `Yᵢ ∈ B` for `Yᵢ`
     near `X`, which is D1's two-sided form near `X`.
   * If D1 stays open, prove continuity at the end sets by another route if you can.
   * Otherwise record exactly which later uses (Lemma 6, the unnumbered claims, Lemma 7, Theorem 1's
     "it follows from Property 1 and Lemma 5" on p. 346) need continuity *at the end sets*, and which
     need only `hagopian76_lemma5_interior`.

**C. Lemma 6** (`hagopian76_closure_extUnion`, `hagopian76_lemma6`) and the unnumbered claims
(`hagopian76_Rset_composant`, `hagopian76_essential_typeA'`).
* Work through steps 1–8 of the batch-156 commission (§2 F).
* Note p. 342: "the decomposition of `F` is a continuous collection (Lemma 5) that has the
  decomposition of `E` as a subcollection". The second half is D1. Record where it is used. Step 6
  ("no element `Y` of the decomposition of `N` has the property that `h₁⁻¹[Y]` contains `N`") is the
  likely place.

**D. Lemma 7.**

**E. The set-up of Theorem 1.**
* `no_proper_subcontinuum_separates`: extract it from `H75Lemma1.lean`.
* `layerKey`, `layerSetoid`, and `layerSetoid_mooreDecomp`. Upper semicontinuity comes from `k` and
  compactness.
* `exists_quotient_plane`: from `m25_theorem22`. The map `π` is the quotient map followed by the
  homeomorphism. `π[E]` is an arc because `t ↦ π(k⁻¹(t))` is a continuous injection of `[0, 1]`.
* `IsAccessibleFrom` and `exists_accessible_typeA'`.
  * Some point of `M` is accessible from `R² − M`. For example, take a point of `M` nearest to a
    point of the unbounded complementary domain, and the straight segment to it.
  * Move that point into an interior layer by a homeomorphism of `M`.
  * The skeleton's `E' = h '' E` is meant as `E'` equal to the image; adjust the coercions as needed.

## 3. Places to check (candidate ledger entries)

1. **p. 341, Lemma 4:** "Since the decompositions of `E` and `F` are minimal, each element of the
   decomposition of `E` (except possibly `k⁻¹(1)`) is an element of the decomposition of `F`" (D1).
2. **p. 341, Lemma 5:**
   * "There exists a type A′ continuum `F` in `R(E)` that is the union of two extensions of `E` such
     that the end sets `T` and `V` of `F` miss `E` (Lemma 4)";
   * "Each element of `A` is contained in an element of `B`. In fact, each element of `A` that is not
     an end set of `E` is an element of `B`";
   * the choice of `h` with (1)–(3);
   * "It follows from Lemma 3 that `h[U] = Yᵢ`".
3. **p. 342:** "the decomposition of `F` is a continuous collection (Lemma 5) that has the
   decomposition of `E` as a subcollection".
4. **pp. 342–343, Lemma 6:** steps 1–8, each with the printed sentence quoted.
5. **p. 343:** the two unnumbered claims.
6. **pp. 343–344, Lemma 7:** "By Lemma 2, an integer `i` and a homeomorphism `f` of `M` onto `M`
   exist such that a continuum `F` essential to `fhᵢ[R(E)]` contains `u`, misses `t`, and intersects
   `A`"; "Note that `g[F] ∪ Hⱼ` is a triod in `M`".
7. **p. 344:** "Hence we can assume that the quotient space `R²/S` is `R²` [12]". Moore 1925
   Theorem 22 gives a quotient homeomorphic to `R²`. Record what "we can assume" hides: `π` is not a
   homeomorphism, and later steps use `π[M]`, `π[Gᵢ]`, `π⁻¹`.
8. **p. 345:** "Since `M` is homogeneous, we can assume without loss of generality that `k⁻¹[(0, 1)]`
   is accessible from `R² − M`." Read it as: some point is accessible. Is "each point of `π[E]` is an
   end point of an arc segment in `R² − π[M]` below `π[E]` (Lemma 9)" a stronger reading that Lemma
   9 then supplies?

## 4. Deliverables

1. Items A–E.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch157.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * **a dependency map of Theorem 1** (pp. 345–349). For each step, say which of Lemmas 2–9,
     Properties 1–4, Mazurkiewicz 1929 and Moore 1962 Theorem 28 it uses. Mark the steps that need D1
     or end-set continuity. If D1 stays open, this map says how far it blocks Theorem 1;
   * a reading plan for batch 158: Lemma 9 and Property 1.
     * Read Bing 1960 p. 215, the definition behind "decomposably accessible from a side", and
       propose a Lean shape for "`Cl A` and `Cl B` abut on the same side of the arc `π[E]`".
     * Moore 1962 Theorem 28, p. 156, is in `doc/sources/moore1962-excerpts.pdf`.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`; sources go to
   `doc/sources/`. Nothing goes at the root.
