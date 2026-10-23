# Commission: batch 158 — Part E, Hagopian 1976 III: D1 by lower semicontinuity; Lemmas 5–7; Moore 1962 Theorem 28; Lemma 9

**Go!** This batch runs on top of the batch-157 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch158.md`: this text, also pasted into the prompt.
* `Hagopian76C.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76C.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76C` at the end of `HPC.lean`.

No new sources are needed.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 III (batch 158)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * `HPC/Hagopian/Hagopian76A.lean` and `Hagopian76B.lean`: delete the commented-out copy of each
    statement proved here, leaving a one-line pointer.

## 0. On batch 157

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1383 lines, with `sorryAx` in none. All 44 new theorems use only the
  standard three axioms.
* **Shape changes accepted:** the definitions moved to `H76BDefs.lean`, and `hi` dropped in
  `exists_accessible_typeA'`.

**Accepted.**
* **The set-up of Theorem 1 in full.**
* **`no_proper_subcontinuum_separates`.** Your observation is recorded in the ledger. The 1975
  argument transports a *non-unicoherent* `F` to every composant; for a separating `K` it needs
  invariance of plane separation, which neither paper states. Your replacement, "a plane continuum
  homeomorphic to a separating compactum contains a separating subcontinuum", avoids Borsuk and
  Brouwer: a logarithm on tree-like continua (Bing 1951 Theorem 6), and no logarithm around a hole.
* **`hagopian76_lemma5_interior`**, `hagopian76_lemma5_usc`, `hagopian76_lemma5_of_ends`.
* **The D1 bookkeeping**, including `k⁻¹(1) ⊆ d⁻¹(s)`.
* **The dependency map of Theorem 1.** It showed that everything from Property 2 on needs D1, and
  that is what this batch fixes.

## 1. D1 is provable: lower semicontinuity of the larger continuum

Your proof of `hagopian76_lemma5_interior` holds for **every** type A′ subcontinuum of `M` with its
minimal map, in particular for an extension `F`. That is the homogeneity input D1 was missing.

Let `F` be an extension of `E` away from `X`, with map `d`, and let `s = max d|E`.
1. If `s = 1`, then `E` meets both end sets of `F`, so `E = F`.
2. Otherwise `0 < s < 1`, and `W = d⁻¹(s)` is a layer of `F` that is not an end set. So the
   decomposition of `F` is lower semicontinuous at `W`.
3. `d⁻¹[[0, s]]` is connected and `d⁻¹([0, s))` is a nonempty proper subset of it. So some
   `y ∈ W` is a limit of points `yᵢ ∈ d⁻¹(uᵢ)` with `uᵢ < s`.
4. By `hagopian76_lemma4_layers'`, each `d⁻¹(uᵢ) ⊆ E` is a single layer of `E`, namely
   `k⁻¹(k yᵢ)`. Also `y ∈ E`, since `E` is closed, and `k yᵢ → k y =: c`.
5. Lower semicontinuity of `F` at `W` gives `W ⊆ liminf d⁻¹(uᵢ)`. Upper semicontinuity of `E`
   gives `limsup k⁻¹(k yᵢ) ⊆ k⁻¹(c)`. Hence `W ⊆ k⁻¹(c)`.
6. Your batch-157 step gives `k⁻¹(1) ⊆ W`. So `c = 1` and **`W = k⁻¹(1)`**.

This gives the strong form `layerSet d (Icc 0 s) = E`, with every layer of `E` a layer of `F`.
* It is the batch-156 rendering, which I had withdrawn as stronger than the printed sentence.
* It is stronger than the printed sentence, and false without homogeneity (the half-bar model), but
  true in this setting.
* It is also what p. 347 uses: "Let `e` be the point of `[0, 1]` such that `d⁻¹[[0, e]] = E`".

Check every step of the argument above. If a step fails, say which one and why.

## 2. Items

**A. `hagopian76_far_layer`, `hagopian76_initial_segment`** (§1). Then derive the printed and
re-rendered forms, so their commented-out copies can go:
* `hagopian76_lemma4_layers` (re-rendered, in `Hagopian76B.lean`);
* `hagopian76_no_swallowed_layer`.

**B. Lemma 5, the end sets.** At `X`:
1. Take an extension of `E` away from `Z`. It is proper, by Lemma 4 applied to the reversed map
   `1 − k`; you have `isAdmissibleMap_symm`.
2. Item A, applied to the reversed map, makes `X` a layer of it that is not an end set, and makes
   the layers of `E` its layers.
3. Lower semicontinuity of that extension at `X` then gives lower semicontinuity of `E` at `X`.
4. Do the same at `Z`, then apply `hagopian76_lemma5_of_ends`.

Hagopian's two-sided `F` is not needed. For `hagopian76_two_sided_extension`, prove it if item A
makes it short (the two extensions meet exactly in `E`); otherwise record that it is not needed.

**C. Lemma 6 and the unnumbered claims.** Formalize steps 1–8 as checked in report 157 §1.C.
* **Step 6** uses "has the decomposition of `E` as a subcollection", which is now item A. Use it in
  the form that the layers of `N` meeting `K` are layers of `K`.
* For `hagopian76_essential_typeA'`, two things are needed:
  * the containment of an essential continuum in one extension. Report 157 called it unargued,
    noting that `R(X, E)` is an increasing union of closed sets; supply it.
  * Lemma 5 at the layers it ends in.

**D. Lemma 7.**

**E. `moore62_theorem28`.** The skeleton reads Moore's "`H` and `K` … subset of `D`" as subsets of
`D ∪ J`, since each meets `J`. Moore's proof, pp. 156–157 in the excerpt, is short. The batch-151
crossing results may also give it directly. Record the route.

**F. `exists_quotient_plane'`, `AbutSameSide`, `DecompAccessible`, `hagopian76_lemma9`.** The
definitions follow your report-157 proposals.

Lemma 9's proof (pp. 344–345) uses four things:
* the chain `G = {G₁, G₂, G₃}` following `E`, with `π[Gᵢ]` open disks and `π[Gᵢ] ∩ π[Gᵢ₊₁]` open
  disks. Saturated open sets have open images under the quotient map;
* Lemma 8, possibly generalized to prescribed caps `A ⊆ G₁`, `B ⊆ Gₙ`, which Property 1 will also
  need;
* Lemma 2;
* item E.

Hagopian also writes "We assume without loss of generality that `π[E]` is lying on a horizontal line
`B` in `R²` and `π[I − {y}]` is below `B` on a vertical line". Supply it from the Schoenflies-type
statement that an arc in the plane can be straightened by a homeomorphism of the plane. If that is
not available, say so and state what is used instead. Moore 1919 and F.A. are in the repository;
check whether an arc-straightening theorem is among them.

If F does not fit in this batch, do A–E first and leave F with a plan.

## 3. Places to check (candidate ledger entries)

1. **p. 341, Lemma 4, first paragraph:** "Since the decompositions of `E` and `F` are minimal, each
   element of the decomposition of `E` (except possibly `k⁻¹(1)`) is an element of the decomposition
   of `F`." Record that the reason given is insufficient (the half-bar model), and that the
   statement, even in the strong form, follows from Lemmas 2 and 3 through lower semicontinuity.
   This is the ledger's verdict: an unargued step, true, supplied by an argument Hagopian does not
   give.
2. **p. 341, Lemma 5:** the two-sided `F` and "each element of `A` that is not an end set of `E` is
   an element of `B`". Record the route actually used.
3. **pp. 342–343, Lemma 6:** steps 1–8, each with the printed sentence quoted, and step 6 in
   particular.
4. **pp. 343–344, Lemma 7:** the two sentences from commission 157 §3.6.
5. **p. 344, Lemma 9:** "We assume without loss of generality that `π[E]` is lying on a horizontal
   line `B` in `R²`"; the chain `G` with `π[Gᵢ]` open disks; "Note that `I` intersects `Bd G₂` and
   misses `Cl (G₁ ∪ G₃)`"; "Since `M` is atriodic and `h(u)` is not in `E`, the sets `G₂ ∩ E` and
   `G₂ ∩ h[E]` are disjoint"; "this is impossible [13, Theorem 28, p. 156]".
6. **p. 347:** "`d⁻¹[[0, e]] = E`" (report 157, check 9). It is now item A.

## 4. Deliverables

1. Items A–F.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch158.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1 updated: what is now unblocked;
   * a reading plan for batch 159: Property 1 and steps T4–T9, T11, T14 of the map.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
