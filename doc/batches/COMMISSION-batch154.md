# Commission: batch 154 — Part F, Jones 1949 VI: Theorems 1 and 2; Jones 1955 Theorem 2 unconditional

**Go!** This batch runs on top of the batch-153 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch154.md`: this text, also pasted into the prompt.
* `Jones49F.lean`: the skeleton.
  * Save it as `HPC/Jones/Jones49F.lean`. You may split it.
  * Add `import HPC.Jones.Jones49F` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Jones 1949 Theorems 1–2; Jones 1955 Theorem 2
    unconditional (batch 154)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 153

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** Five statements are verbatim, and `theta_of_cyclic_peano` takes the shape you
  chose.
* **Audit.** `axioms.txt` has 1196 lines, with `sorryAx` in none.

The results:
* **Whyburn 1939 Corollary 1 is verified.**
* The arc theorem is proved in its open-set form, by Moore's `exists_irreducible`.
* `frontier_cyclic` is proved by a Janiszewski argument, and needs only compactness and cyclicity.
* There is a θ-curve in every cyclic Peano continuum that is not a circle.
* The θ-curve lemma is proved from `jordan_curve_theorem` alone.

The ledger records the following:
* footnote 16's equivalence with Wilder's local 0-avoidability, as unargued, not decided and not
  used;
* Wilder's first corollary to Theorem 8a, as having the same conclusion.

## 1. Where this sits

This batch closes Part F. When `jones49_theorem1 : Jones49Thm1` is proved, the hypothesis `h49` is
discharged from batch 148. Jones 1955 Theorem 2 and its closing remarks then become unconditional.
After that, nothing in the Jones line depends on an unproved statement.

## 2. Items

Follow your batch 153 §5 plan.

**A. `jones49_setting`, `jones49_simple_domains`.**

**B. `jones49_case1`.** The steps:
1. the images of `J` under homeomorphisms of `M`;
2. the passage to the boundary of an element of `G`, with `jordan_curve_theorem` and
   `conn_sub_of_frontier`;
3. `G` countable;
4. Baire;
5. an arc neighbourhood gives order 2.

**C. `jones49_case2`.** The steps:
1. the arc `T` (`exists_tarc_of_isOpen_plane`, first-point trims);
2. the element `U`;
3. `C ∩ J ≠ ∅`;
4. the arc `AxB`;
5. `M − (A + B)` not connected, which is the main new step;
6. `M − B` connected;
7. `A` is a local separating point, with the separation of `M − B` in Whyburn's sense, since `M − B`
   is connected.

**About step 5.** It is not worked out in your plan. Here is a start, for you to check or replace.
* `J ∪ AxB` is a θ-curve with vertices `A`, `B`. Since `M ∩ D = ∅`, `AxB − {A, B} ⊆ H` lies on the
  side `E` of `J` other than `D`, and splits `E` into `E₁` (bounded by `J₁ + AxB`) and `E₂` (bounded
  by `J₂ + AxB`), where `J₁`, `J₂` are the open arcs of `J` from `A` to `B`.
* `U` misses the θ-curve, so `U` lies in `E₁`, say. The other end `y` of `T` lies in `K` and in
  `Ū − θ`, hence in `E₁`.
* The difficulty is `AxB − {A, B}`. It lies in the closure of both `E₁` and `E₂`, so the naive
  partition `M ∩ (E₁ ∪ J₁)`, `M ∩ (E₂ ∪ J₂ ∪ AxB°)` need not be separated.
* Use instead that `AxB` lies on `C = ∂U` with `U ⊆ E₁`, and that `H`, `K` are separated in `M − J`.
* If the step is false as Jones states it, say so with the configuration. If it is true but needs
  more of the hypotheses (homogeneity, no point of order 2), record which.

**D. `jones49_theorem1`.** In both cases some point has order 2:
* Case 1 is a contradiction;
* Case 2 goes by `jones49_some_order_two`.

Then `jones49_order_two` concludes.

**E. `jones49_theorem2`**, through Jones 1948 Theorem 18 (`theorem18`), homogeneity, and item D.
Record the degenerate case: a point has no weak cut point, so the printed Theorem 2 fails for a
one-point continuum, exactly as Theorem 1 does.

**F. The unconditional Jones 1955 results:**
* `jones55_theorem2'`;
* `jones55_two_domains'`;
* `jones55_elements_indecomposable'`;
* `jones55_three_domains'`.

Each is the batch 148 theorem applied to `jones49_theorem1`.

## 3. Places to check (candidate ledger entries)

All are from page images, Jones 1949 pp. 113–114. The A.18 entries of my ledger list the gaps.

1. **Case 1:** "each point of `M` belongs to some such simple closed curve lying in `M`.
   Consequently each point of `M` belongs to the boundary of an element of `G`". Record how the gap
   is supplied.
2. **Case 1:** "Since no point of `M` is of order 2 in `M`, each point of `Jᵢ` is a limit point of
   `M − Jᵢ`." Record the argument.
3. **Case 2:**
   * "There exists an arc `T` lying in the complement of `D̄` which is irreducible from `H` to `K`."
   * "Except for its end points, `T` lies in an element `U` of `G`."
   * "The component `AxB` of `C − C·J` which contains `x` is an arc-segment whose end points lie on
     `J`." This needs `C ∩ J ≠ ∅`.
   * "It follows that `M − (A + B)` is *not* connected".
4. **Case 2:** "Since `M` is homogeneous, every point of `M` is a local separating point of `M`. But
   all except countably many of the local separating points of `M` must be of order 2 in `M` [8]."
   Note that this needs `M` uncountable, which is unstated.
5. **Theorem 2's proof:** "Being aposyndetic at one point, `M` must be aposyndetic at each of its
   points." This is homogeneity, and it is tacit.
6. **The degenerate cases** of Theorems 1 and 2.

## 4. Deliverables

1. Items A–F.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch154.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a closing inventory of Part D–F (Jones 1955 Theorem 2 through all its dependencies). List every
     source result used, by file and theorem name, with its status: verified, verified with
     corrected hypotheses, or replaced by a different argument. Also list every remaining
     non-standard axiom or hypothesis, which should be none.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
