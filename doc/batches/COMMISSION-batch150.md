# Commission: batch 150 — Part F, Jones 1949 II: Whyburn's order theorems; Moore 1922

**Go!** This batch runs on top of the batch-149 delivery. Four files come with it, as separate
uploads:

* `COMMISSION-batch150.md`: this text, also pasted into the prompt.
* `Jones49B.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones49B.lean`. You may split it.
  * Add `import HPC.Jones.Jones49B` at the end of `HPC.lean`.
  * It restates the two items left open in batch 149, `whyburn_9_2` and `jones49_some_order_two`,
    verbatim. When they are proved, delete their commented copies in `HPC/Jones/Jones49A.lean` and
    update `OPEN.md`.
* `moore1922.pdf`: R. L. Moore, *Concerning connectedness im kleinen and a related property*, Fund.
  Math. 3 (1922), 232–237. This is the scan, which has no text layer.
* `moore1922-transcription.pdf`: my typeset transcription of it from 200-dpi images.
  * Moore's wording and misprints are kept, and editorial notes are in blue.
  * Use it for reading. Check against the scan before quoting.

Save both PDFs to `doc/sources/`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `HPC/Jones/Jones49A.lean` (only to delete the two commented statements, once they are proved);
  * `Axioms.lean` and `axioms.txt` (new group "Whyburn Ch. III; Moore 1922 (batch 150)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`.

## 0. On batch 149

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** Eight are verbatim. `whyburn_9_1` drops `hR`, which makes it stronger and is
  accepted. Two are left open as comments, as the commission allowed.
* **Audit.** `axioms.txt` has 1128 lines, with `sorryAx` in none.

The results:
* **Menger's theorem**, by his own second argument on p. 267 used twice. This route is better than
  either of mine, and it avoids the unargued steps of his p. 266 route. The ledger records those
  steps.
* **`tscc_homeomorph_circle`.**
* **Whyburn (9.1)**, with its proof's misapplication of [I, (10.2)] repaired. The ledger counts this
  as a defective proof, which brings the total to twelve.
* **The definitions checked against Menger p. 97 and Whyburn p. 48.**

**Your batch 150 proposal is adopted.** This batch formalizes Ch. III §§1–3 and (8.2)–(8.41) once,
which closes (9.2) and `jones49_some_order_two`, and it adds Moore 1922. Whyburn 1939 §14 moves to
batch 151.

| batch | content |
|---|---|
| **150 (this one)** | Whyburn (3.2), (8.4), (8.41), (9.2), `jones49_some_order_two`; Moore 1922 Theorems 1–4 |
| 151 | Whyburn 1939 §14, Theorem and Corollary 1 (complementary domains of a cyclic s.l.c. plane continuum are bounded by simple closed curves) |
| 152 | Jones 1949 Cases 1 and 2; `jones49_theorem1 : Jones49Thm1`; Jones 1955 Theorem 2 and its closing remarks unconditional |

## 1. Items

**A. Whyburn, Ch. III.**
* `whyburn_3_2`, for compact metric continua. Whyburn's (3.1) and (3.2) are stated for connected
  sets with "potential order" and for generalized continua with "order".
  * Formalize the ordering of §1 ((1.31)) and the non-separated cuttings of §2 ((2.2)–(2.22)) as far
    as (3.2) needs them.
  * Record Whyburn's definitions of *generalized continuum* (Ch. I) and of *potential order*
    (Ch. III §2).
* `whyburn_8_4`, through (8.1)–(8.32).
* `whyburn_8_41`, `whyburn_9_2`, `jones49_some_order_two`. The last one comes through batch 149's
  `jones49_some_order_two_of_whyburn_9_2`.

**B. Moore 1922.**
* Theorems 1–3. They are short.
* Theorem 4 in both directions. Batch 151 uses only *property S ⇒ locally connected boundary*.
  * **Sufficiency** cites "the argument beginning with the second line from the bottom of page 365
    and ending in the twenty third line from the top of page 366" of Moore, *A characterization of
    Jordan regions by properties having no reference to their boundaries*, PNAS 4 (1918), 364–370.
    I do not have this paper. Reconstruct the argument: from a boundary point `P` where `M` is not
    locally connected, get two circles about `P` and infinitely many disjoint continua of `M`
    crossing the annulus. Record what it needs. If it is long, say so in the report and I will try
    to obtain PNAS 4.
  * **Necessity** is complete in the text, up to the slips listed in §2.

## 2. Places to check (candidate ledger entries)

These were found while I transcribed Moore 1922 from the page images (200 dpi; damaged subscripts at
400 dpi).

1. **p. 233, Theorem 1's proof:** "For each `n` there exists a connected point-set `tₙ` which
   contains `Aₙ` and `Pₙ`, is a subset of `M` and lies wholly within `K*`." By the choice of `K*`,
   the set should lie within `K̄`. As printed, the limit set `t` need not lie within `K`.
2. **p. 234, Theorem 2's proof:** the set is called `M_s` and then `M_t` (damaged subscripts). Record
   it if it is real. Note also: "`M_t + P` is a connected subset of `M`, of diameter less than `ε`".
   This uses `P ∈ closure M_t`, and the diameter is unchanged.
3. **pp. 234–235, Theorem 3's proof:** "But these connected point-sets are all of diameter less than
   `ε`". `M_K` is a union of connected sets of diameter `< ε` through `P`, so its diameter is only
   `≤ 2ε`. This is harmless with `ε/2`. Record it.
4. **p. 236, Theorem 4's proof:**
   * "the point-set `t_m` contains at least one point `A_m` on `K*`": this should be `t̄_m`.
   * "For each positive integer `m (1 ≤ m ≤ n)`": this should be `1 ≤ m ≤ 4ⁿ`.
5. **p. 237, Theorem 4's proof:** "Let `ε = (b − c)/4`", where `b` and `c` are the sides of
   `K_m̄` and `T_m̄`. Since `b < c` this is negative; presumably `(c − b)/4`. Record also the other
   unargued steps:
   * "every `R_{m̄P_i}` has at least one limit point on the square `T_m̄`";
   * "For each `n` the boundary of `R_n` contains a closed connected subset `R̄_n` such that …";
   * "It can easily be seen that no two of the sets `R̄₂, R̄₄, …` have a point in common".
6. **p. 236:** "Since `R` does not have property `S` and each set `R_{mP}` is of diameter less than
   `ε` there must exist at least one value `m̄` … such that no two of the connected sets
   `R_{m̄P₁}, R_{m̄P₂}, …` have a point in common". This needs that the `R_{mP}` for a fixed `m`
   are either equal or disjoint (they are components). Record it.
7. **Typographical:** "fie" for "lie" (p. 233), "curce" for "curve" (p. 235), "a sumed" (p. 234,
   footnote).
8. **Whyburn (3.2)** and **(8.4)**: record the steps that are unargued, as in batch 149's ledger
   entry for (9.2).

## 3. Deliverables

1. Items A and B.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch150.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for batch 151: Whyburn 1939 §14 (`doc/sources/whyburn1939.pdf`, pp. 747–749).

   For the reading plan:
   * The Theorem's proof applies Moore 1922 to "each complementary domain `R`". Moore's Theorem 4
     is for *bounded, simply connected* domains. Say how the unbounded complementary domain is
     handled, and whether each bounded complementary domain of a continuum is simply connected in
     Moore's sense.
   * Say what (6.22) and the F.A. theorem that §14 uses require.
   * Say how Corollary 1, which is stated without proof, follows: a locally connected boundary of a
     complementary domain of a cyclic plane continuum is a simple closed curve.
4. Housekeeping: uploads go to `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`. Nothing
   goes at the root.
