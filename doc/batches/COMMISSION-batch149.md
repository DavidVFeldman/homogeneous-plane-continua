# Commission: batch 149 — Part F, Jones 1949 I: order, Menger's theorem, Whyburn (9.2)

**Go!** This batch runs on top of the batch-148 delivery. Four files come with it, as separate
uploads:

* `COMMISSION-batch149.md`: this text, also pasted into the prompt.
* `Jones49A.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones49A.lean`. You may split it.
  * Add `import HPC.Jones.Jones49A` at the end of `HPC.lean`.
* Two sources (both cited by Jones 1949, and both missing when you wrote the reading plan). Save them
  to `doc/sources/`:
  * `menger-kurventheorie.pdf`: K. Menger, *Kurventheorie*, 2nd ed., Chelsea 1967. It has the same
    pagination as the 1932 edition Jones cites; p. 267 is PDF p. 275.
  * `wilder1938.pdf`: R. L. Wilder, *Sets which satisfy certain avoidability conditions*, Časopis 67
    (1938), 185–198. This is for batch 150.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Jones 1949: order, Menger, Whyburn 9.2 (batch 149)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 148

Audited and accepted.
* The skeleton and commission copies are byte-identical. All 19 declarations are verbatim, except
  for the `open Function in` added before `countable_of_pairwiseDisjoint_open`, which is accepted.
* `axioms.txt` has 1113 lines, with `sorryAx` in none.

What batch 148 delivered:
* **The plane Jordan curve theorem** as a corollary of Moore 1925 Theorem 11, by way of the
  decomposition into points. This does not depend on `m19_plane`.
* **Jones 1955 Theorem 2, conditional on `Jones49Thm1`.** Only conclusion (1) uses the hypothesis.
  The closing remarks are also proved, under the same hypothesis.
* **The disjointness of the domains `W_g`,** which Jones does not argue.

Your Whyburn finding is confirmed from the page image: Jones's "Theorem 9.1, p. 61" is (9.2). Your
convention finding (Whyburn Ch. I §10 admits one-point continua) makes Jones 1949 Theorem 1 false as
printed for a point. The ledger now counts twenty printed statements false.

Your four-batch plan is adopted, with one change: **this batch takes (i) and (iv) together**, since
they are independent and each is estimated at about 600 lines. If time runs short, deliver (i)
complete and leave the items of (iv) open, with their obstruction stated in `OPEN.md`.

| batch | content |
|---|---|
| **149 (this one)** | (i) order; `TSCC ⇒ ≃ₜ Circle`; Menger p. 267; (iv) Whyburn (9.1), (9.2) |
| 150 | (iii) Whyburn 1939 §14 and Corollary 1 / Wilder 1938 Theorem 8a; Moore 1922 (property S) |
| 151 | (v) Jones 1949 Cases 1 and 2; `jones49_theorem1 : Jones49Thm1`; Jones 1955 Theorem 2 unconditional |

## 1. Items

**A. Order.**
* Check `OrderLE` and `HasOrder` against Menger's definition of *Ordnung* (*Kurventheorie* Ch. IV;
  locate it) and Whyburn's (Ch. III §2, p. 48). Record any difference. Jones's "of order 2 in `M`"
  refers to these books (his footnote 3).
* `hasOrder_homeomorph`.

**B. `tscc_homeomorph_circle`.** Glue two arcs along their ends. This is the converse of batch 148's
`tscc_circle`.

**C. Menger.**
* `menger_order_two`: a nondegenerate compact metric continuum all of whose points have order 2 is a
  circle. Choose the shorter of two routes:
  * your direct route through `circle_char`. Its steps are: local connectedness from finite order;
    no cut points; every two points separate.
  * Menger's own: pp. 262–267, regular curves, and the *Kennzeichnungstheorem* of ordinary curves.
    Read it first.

  Record which route you took.
* `jones49_order_two`: homogeneity together with `hasOrder_homeomorph`.

**D. Whyburn.**
* `IsSepPointOf` and `IsLocalSepPoint` (p. 61). Check the skeleton's reading of "separating point of
  an open set `R`" against Whyburn's usage in Ch. III §§8–9, and record it.
* `whyburn_9_1`.
* `whyburn_9_2`, through (8.4), (8.41) and the non-separated cuttings of §§2 and 8.
* `jones49_some_order_two`. If the full (9.2) is long, a direct proof of this consequence alone is
  acceptable; then leave `whyburn_9_2` open, with the obstruction stated. Jones uses only the
  consequence.

## 2. Places to check (candidate ledger entries)

All are transcribed from page images.

1. **Jones 1949, p. 113:** "If a point of `M` is of order 2 in `M`, then `M` is a simple closed curve
   [4]". Menger's theorem needs *all* points of order 2. Record that homogeneity and the invariance
   of order are tacit. The ledger already has this as harmless.
2. **Menger p. 267**, the theorem and its proof: record what it rests on in Menger (pp. 262–266),
   and any step there that is unargued.
3. **Whyburn (9.1), proof:** "it follows by [I, (10.2)] that the components `V₁` and `V₂` of
   `U·(Q·R_a + p)` and `U·(Q·R_b + p)`, respectively, containing `p` are nondegenerate". This is a
   boundary-bumping step; record it.
4. **Whyburn (9.2), proof (pp. 61–62):** record the steps, and any that are unargued.
5. **Whyburn (8.41):** "each separating point of `L` lies in some `L_i` and is a separating point of
   `L̄_i`". Check it. A separating point of `L` need not separate the closure of a small open piece
   unless the reading of "separating point" makes it so.

## 3. Deliverables

1. Items A–D.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch149.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 150: Whyburn 1939 §14 (Theorem, Corollary 1), Wilder 1938 Theorem 8a
     and its first corollary, and Moore 1922 (property S; Fund. Math. 3). I do not have Moore 1922.
     Say whether Whyburn's or Wilder's route avoids it, or whether I should find it.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
