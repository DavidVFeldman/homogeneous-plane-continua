# Commission: batch 166 — Part E, Hagopian 1976 XI: Theorem 1 — `D`, `K₀`, Property 3, T12, T13; then T15–T17 and the assembly

**Go!** This batch runs on top of the batch-165 delivery. Two files come with it, as separate
uploads:

* `COMMISSION-batch166.md`: this text, also pasted into the prompt.
* `Hagopian76K.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76K.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76K` at the end of `HPC.lean`.

No new sources are needed. Mazurkiewicz 1929 is already in `doc/sources/mazurkiewicz1929.pdf`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XI (batch 166)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers.

**Progress lines.** As in batch 165, write a `STATUS:` line in your trace whenever an item is proved,
left open, or stuck. If a hint would help, write `STATUS: need help` and the obstruction in one
sentence.

## 0. On batch 165

Audited and accepted. All of it.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 1686 lines, with `sorryAx` in none, all on standard axioms.
* **Housekeeping.** The ten stale copies of the notes are deleted. Thank you for the build
  provenance.

**Accepted.**
* `hagopian76_no_hair`, `preimage_pi_isContinuum` (with your fibre lemma), `rect_crossing` (with your
  `U` frame), and `hagopian76_T7`, with `hγ` dropped.
* `exists_isEps1_endCtl` and `hagopian76_link_control`.
* `hagopian76_T8`, which gives property (D), and `hagopian76_T9_full`.
* **`hagopian76_T11` for the whole section `π⁻¹[D ∩ ⟨p₃, q₃⟩]`.** Your channel objection to the
  single component `K` is right. If `I₂` crosses the vertical over `p₃` three times, part of `D` lying
  left of `p₃` is joined to the right side above the lowest crossing. The ledger records Hagopian's
  sentence as unargued and not needed.

## 1. Notes on the items

**A. `D` as a Jordan domain** (`rect_domain`, then `hagopian76_D`). Work in collar coordinates.
* The curve `J = I ∪ [a, b] × {0} ∪ {a} × [0, r₂] ∪ {b} × [0, s₂]` is a simple closed curve. `I`
  meets the side edges only at `r` and `s`, and misses the bottom edge.
* By `jordan_curve_theorem`, `J` has a bounded complementary domain `D′`.
* `D′` lies in the open rectangle, because the complement of the closed rectangle is connected,
  unbounded and misses `J`.
* `D = F[D′]` is open, because `F` maps the open rectangle onto an open set and is injective there.
  Its frontier is `F[J]`.
* Record that `D` is Hagopian's "bounded complementary domain of `I₂ ∪ ⟨p₁, p₅⟩ ∪ ⟨p₁, r⟩ ∪ ⟨p₅, s⟩`".

**B. `K₀`.** Let `w` be the lowest point of `I₂` on the vertical over `11/22`; it exists because
`I₂ ∩ vertical` is compact and nonempty. Put `K₀ = π⁻¹F[{11/22} × (0, w₂)]`. It is Hagopian's `K`:
the component of `π⁻¹[D ∩ ⟨p₃, q₃⟩]` whose closure meets `π⁻¹(p₃)` and `π⁻¹[I₂]`. T12 uses `K`
only through points `p`, `q` near `x ∈ k⁻¹(11/22) ∩ Cl K`, and through "an arc in `K`"; both lie in
`K₀`. Wherever a separation by `K` is used, use `hagopian76_T11` for the whole section, and say so.

**C. "`L − {L₁, L₁₁}` follows `Cl B`."** A route; check it.
1. By `hagopian76_T9_full`, `Cl B = h[G]` with `G ⊆ E` a subcontinuum, and `Cl B ∩ E = ∅`.
2. `B` is a component of `M ∩ π⁻¹[D]`. If a point of `Cl B` that is an end of `h[G]` (in the order
   of `h[E]`) lay in `π⁻¹[D]`, then `h[E]` would continue `B` inside `π⁻¹[D]`, unless that end were
   an end set of `h[E]`. End sets of `h[E]` lie in `L₁ ∪ L₁₁`, which property (D) excludes. So both
   ends of `Cl B` lie on the frontier of `π⁻¹[D]`.
3. The frontier part met by `M` is over the two open side edges. `I₂` misses `π[M]`, and `Cl B`
   misses `E`.
4. Both ends cannot be on the same side. Link control puts a point over the left edge in links of
   Lean index `≤ 2`. Property 1 (`h[piece (j + 1)] ⊆ L j`) then puts both ends in the first four
   pieces of `h[E]`, so `Cl B` would lie in `L₁ ∪ … ∪ L₄`.
   * That still allows `L₄`. If the margin is one link short, use the finer abscissa bound of
     `hagopian76_link_control` with a smaller `η`, or restrict to components meeting `L₅ ∪ … ∪ L₇`.
     Then check what T12 and T17 use.
5. With one end on each side, `h[G]` runs through all of `L₂, …, L₁₀` in order.

**D. Property 3.** Take the plan of reports 164 §1.6 and 165 §1.E, now with `D` and its side edges.
* **The least `v`.** Crossing components in the layer `d⁻¹(vₙ)`, with `vₙ ↓ v`, have closures
  that converge (on a subsequence, in the hyperspace) to a continuum `Z` in `d⁻¹(v)`. This uses
  upper semicontinuity of the layers of `d`.
  * `Z` meets both side preimages. It misses `π⁻¹[I₂]` by `ε₂`, and misses `E` by
    `hagopian76_no_hair`.
  * So `Z ∩ π⁻¹[D]` has a component whose closure meets both sides. Use boundary bumping in `Z`,
    from a point over one side towards the other.
  * Say whether "first point" needs the infimum to be attained, or only a crossing at some `u < v`
    for the contradiction.
* **The crossing property under the shift `g`.** "By Lemmas 2 and 3" is
  `hagopian76_property3_shift`. What remains is that `g` maps a crossing component to a crossing
  component when `g` is close enough to the identity. Crossing means reaching from over `⟨p₁, r⟩` to
  over `⟨p₅, s⟩` inside `π⁻¹[D]`. This is not automatic for a small `g`: the image may touch
  `π⁻¹[I₂]` or leave `π⁻¹[D]`. If Hagopian's sentence needs a margin, say which (for example,
  crossing components of `F ∩ π⁻¹[D′]` for a slightly smaller `D′`), and adjust the shape.

**E. T12, and "distinct inaccessible composants [10]".**
* Hagopian picks `p`, `q` in `K ∩ (W − R(E))` "that belong to distinct inaccessible composants [10]
  of the indecomposable continuum `Cl R(E)` (Lemma 6)". `[10]` is Mazurkiewicz 1929, which is not
  formalized.
* **Before formalizing it, find out what "inaccessible" is used for in T12–T17.** If only "distinct
  composants, both different from the composant `R(E)`" is used, then this follows from the fact
  that a nondegenerate indecomposable continuum has uncountably many composants. Each composant is a
  countable union of proper subcontinua, which are nowhere dense.
  * You then need points of `K₀ ∩ W` outside `R(E)` and in two distinct composants. `K₀` is an arc
    whose closure meets `k⁻¹(11/22)`. Check whether `K₀ ∩ Cl R(E)` near `x` is large enough; this
    is not obvious.
  * If accessibility is used, state exactly where, and give the statement needed from Mazurkiewicz
    as a separate item. Its proof can then be its own batch.
* "By Property 1, `R(E)` intersects an arc in `K` that is irreducible between `C` and the
  `q`-component of `M ∩ π⁻¹[D]`, and `R(E)` separates these components in `π⁻¹[D]`" is unargued.
  Check it.

**F. T13**, its existence sentence, then T15–T17 and `hagopian76_theorem1`, if reached.

## 2. Order

A, B, C, D, E, F. If E's use of Mazurkiewicz needs the theorem itself, state the needed statement as
a `Prop` definition (as `Hagopian76Thm1` is). Prove T13–T17 with it as a hypothesis, and say so.

## 3. Places to check (candidate ledger entries)

1. **p. 346, T8:** "Let `D` be the bounded complementary domain …".
2. **p. 346, T9:** "Note that the chain `L − {L₁, L₁₁}` follows `Cl B`".
3. **p. 347, Property 3:** "Let `v` be the first point …"; "By Lemma 1 and Property 1, `L` follows a
   type A′ continuum in `d⁻¹(v)` that meets `L₆ ∩ π⁻¹[D]`"; "This contradicts the definition of
   `v`".
4. **p. 347, T12:** "Let `p` and `q` be points of `K ∩ (W − R(E))` that belong to distinct
   inaccessible composants [10]"; "By Property 1, `R(E)` intersects an arc in `K` …".
5. **p. 347, T13:** "The existence of such a continuum `F` follows from Property 1 and the fact that
   `Cl R(E) = Cl R(k⁻¹(0), E)` (Lemma 6 (proof))".
6. **pp. 347–349, T15–T17**, if reached. In particular: "It follows from Property 3 that `I` is
   finite"; and the induction "Following Bing [2, p. 225]".

## 4. Deliverables

1. The items of §2.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch166.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * if F is not finished, a skeleton proposal for what remains.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`. Nothing goes at the root.
