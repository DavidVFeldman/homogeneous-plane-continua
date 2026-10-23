# Commission: batch 155 — Part E, Hagopian 1975 I: Lemmas 1–4, the type A′ subcontinuum, interior layers

**Go!** This batch runs on top of the batch-154 delivery. Five files come with it, as separate
uploads:

* `COMMISSION-batch155.md`: this text, also pasted into the prompt.
* `Hagopian75.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian75.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian75` at the end of `HPC.lean`.
* Three sources, for `doc/sources/`:
  * `hagopian1975.pdf`: C. L. Hagopian, *Homogeneous plane continua*, Houston J. Math. 1 (1975),
    35–41;
  * `kuratowski2-s48.pdf`: Kuratowski, *Topology* Vol. 2 (1968), §48, pp. 190–220;
  * `moore1962-excerpts.pdf`: Moore, *Foundations of point set theory*, rev. ed. (1962), pp. 15,
    49–50, 58–59, 156, 172–175, 214–223.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1975 (batch 155)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`, only if something is left open.

## 0. On batch 154

Audited and accepted.
* **Copies.** The skeleton and commission copies are byte-identical.
* **Statements.** All ten statements are verbatim.
* **Audit.** `axioms.txt` has 1221 lines, with `sorryAx` in none. Nothing is open.

**Part D is complete.** `jones49_theorem1 : Jones49Thm1` is proved, and Jones 1955 Theorem 2 and its
closing remarks hold with no `h49`.
* Your proof that Case 2's "`M − (A + B)` is *not* connected" is true as Jones states it, by
  θ-curves, the no-common-side lemma and Janiszewski, is accepted.
* The closing inventory (461 results, no non-standard axiom or hypothesis) is accepted.
* The ledger counts Jones 1949 Theorem 2 at a point as the twenty-first statement false as printed.

## 1. Where this sits

Part E (indecomposable homogeneous plane continua) starts here. Its order is forced by the
citations:

| batch | content |
|---|---|
| **155 (this one)** | Hagopian 1975, the parts Hagopian 1976 uses |
| 156– | Hagopian 1976 (Trans. AMS 224, 339–350): an indecomposable homogeneous plane continuum is hereditarily indecomposable |
| later | Rogers 1981 (separating ⇒ decomposable; it cites Hagopian 1976), then Oversteegen–Tymchatyn |

Hagopian 1976 cites four parts of this paper:
* Lemma 1;
* Lemma 3;
* the proof of Lemma 4;
* paragraphs 1–3 and 9–11 of the proof of Theorem 1.

**Paragraph 4 of that proof is set aside.** It needs Bing 1960 (Canad. J. Math. 12: a homogeneous
bounded plane continuum containing an arc is a simple closed curve), and 1976 does not use it. In
the skeleton, paragraph 4 is the hypothesis `hnd` of `hagopian75_theorem1_of_layer`.
* Theorem 1 as printed, its Corollary and Theorem 2 will follow after Hagopian 1976, as will Bing
  1960 for plane continua (an arc is decomposable).
* Say whether you see an obstruction to that.

**Thomas 1966** (Rozprawy Mat. 50) is cited for type A and A′ and is not in hand. Kuratowski §48
replaces it for type A′, which is all that is used. Lemma 3 is asked for in its type A′ form. The
printed type A form is not asked for.

## 2. Items

Follow the skeleton.

**A. Definitions.** `IsTriodSet`, `IsAdmissibleMap`, `IsTypeA`, `IsTypeA'`, `layer`, and
`admissible_quotient_homeomorph`.
* An admissible decomposition is taken in map form: a continuous surjection onto `[0, 1]` with
  connected fibres.
* The theorem justifies this against Hagopian's wording on p. 36 ("upper semi-continuous
  decomposition … whose quotient space is the unit interval"). Record the argument in both
  directions, even though only one is formalized.

**B. Composants** (Moore Theorems 135–139, pp. 58–59): `composant_dense`, `composant_eq_or_disjoint`,
`composant_isMeagre`, `uncountable_composants`. Reuse `HPC/PseudoArc/Theorem13.lean` and
`HPC/Jones/Basic.lean` where they apply.

**C. `moore_triod_theorem`** (Moore Theorem 84, p. 222): the plane contains no uncountable family of
mutually exclusive triods.
* Moore's route uses his Theorems 73, 76, 78, 79 (pp. 217–221). It needs his Chapter IV
  apparatus, and the excerpt does not contain all of that.
* Any route is acceptable: Moore's, the usual one through three rational discs and a θ-curve, or
  your own.
* Prove it from `jordan_curve_theorem` and the batch 146–153 plane tools, and record the route.
* Also bridge `IsTriodSet` (in the plane) to `HPC.Plane.IsTriod` (in the subtype `M`).

**D. `hagopian75_lemma1`.** First paragraph:
* a triod in `M` is a proper subcontinuum, since `M` itself is not a triod (`M` is indecomposable);
* homeomorphisms permute composants;
* a triod in each composant gives uncountably many disjoint triods;
* item C.

Second paragraph:
* `janiszewski_compact` or `plane_unicoherent` gives that `F` separates the plane;
* the "separable" step;
* the contradiction with density.

A sketch of the "separable" step, for you to check or replace:
* For each composant `κ`, let `F_κ ⊆ κ` be a homeomorphic copy of `F`. Suppose each `F_κ` has a
  complementary domain `U_κ` missing `M`.
* Two such domains are then disjoint. Since `F_κ ∩ F_κ' = ∅`, the domain `U_κ` lies in one
  complementary domain of `F_κ'`. If that domain were `U_κ'`, then `∂U_κ ⊆ F_κ` would lie in
  `closure U_κ' ⊆ U_κ' ∪ F_κ'`, which misses `M`.
* So there are uncountably many disjoint open sets, which contradicts separability.
* Hence some `F_κ` has at least two complementary domains, and every one of them meets `M`.

The density step:
* A composant `κ'` other than `κ` meets `U ∩ M`. Choose it by Baire, using `composant_isMeagre`.
* `κ'` is dense, so it meets `V`.
* A proper subcontinuum joining the two points crosses `F_κ`, so its union with `F_κ` is proper
  (Moore 138's argument), and `κ' = κ`.

Record what Hagopian leaves out.

**E. `hagopian75_lemma2`** (both directions), `admissible_end_sets`, `layer_subset_of_meets`.
* Necessity: an indecomposable subcontinuum with interior is a closed domain that produces a jump
  (Kuratowski VII Theorem 1, p. 214). Or argue directly from the layers: if `k(K)` is a point, a
  layer has interior. If `k(K) = [d, e]` with `d < e`, then `K ⊇ k⁻¹((d, e))` by
  `layer_subset_of_meets`, and you must show `K` is decomposable.
* Sufficiency is Kuratowski §48: III (the family `D`), IV (the function `g`, the layers), and VII,
  Theorems 1–5. Theorem 3 (p. 216) is about the order type of `D`. Record how it passes to a
  monotone map onto `[0, 1]` with nowhere dense layers, or prove sufficiency directly if that is
  shorter.

**F. `hagopian75_lemma3`, `hagopian75_lemma3_unique`, `arc_of_degenerate_layers`.**
* For Lemma 3, Kuratowski's proof of Theorem 4 (pp. 216–217) shows that any monotone map onto
  `[0, 1]` sends a nowhere dense continuum to a point. That is the step.
* `arc_of_degenerate_layers` is Kuratowski VII Theorem 6 in the form Thomas 21 is cited.

**G. `hagopian75_lemma4`**, from `effros_homogeneous` (take `W` a ball of radius `δ/2`). Note how
this differs from Hagopian's route, which uses Effros's Theorem 2.1 and the open map `T_x`.

**H. `hagopian75_no_indecomposable_interior`, `hagopian75_exists_typeA'`.** These are paragraphs
1–3.
* Write out the triod `B ∪ F ∪ f[F] ∪ g[F]`: its core, its three pieces, and why they are separated.
* Write out why `F`, `f[F]` and `g[F]` are mutually disjoint. Hagopian gives neither.
* If the argument needs a different choice of `f`, `g` (for example, `f(x)` and `g(x)` in composants
  of `I` other than the one `F` meets), say so.

**I. `hagopian75_layer_invariant`** (paragraphs 9–11). Then `hagopian75_layer_homogeneous`
(paragraphs 5–8 and 12).

**J. `indecomposable_of_unicoherent_homogeneous`** (paragraph 13), from `jones55_theorem2'`.

**K. `hagopian75_theorem1_of_layer`.**

## 3. Places to check (candidate ledger entries)

All are from page images, pp. 35–40.

1. **p. 35:** "a *continuum* is a nondegenerate compact connected metric space". Record which
   statements need nondegeneracy, given the repository's `IsContinuum`, which allows a point.
2. **p. 36, Lemma 1:** "Since `M` is homogeneous, it follows that each of its composants contains a
   triod." This needs the triod to be proper.
3. **p. 36, Lemma 1:** "Since the plane is separable and `M` has uncountably many composants, there
   exists a proper subcontinuum of `M` having two complementary domains that intersect `M`. This
   contradicts the fact that each composant is dense in `M`." Both steps are unargued. Record what
   supplies them: disjointness of the domains, Baire, Moore 138.
4. **p. 36:** Hagopian defines a decomposition as a collection of *compact* sets, and type A by
   elements that are "connected sets". Record that the map form agrees.
5. **pp. 36–37, Lemma 2:** "[10, Theorem 3, p. 216]". Kuratowski's Theorem 3 states that the family
   `D` has the order type of the interval, not that the continuum is of type A′. Record what fills
   the gap.
6. **p. 37, Lemma 3:** it is printed for type A and cites Thomas. Record that only the type A′ form
   is proved and used.
7. **p. 37:** the misprint "*transfromation*". Also, Effros's Theorem 2.1 is used as "each orbit is
   a set of the type `G_δ` … iff … homeomorphism". Record that the repository's Effros is the
   open-mapping form.
8. **p. 38, Theorem 1:** "Since `M` is hereditarily unicoherent and `I` is indecomposable, `I` is
   contained in `E ∩ B` or `E ∩ C`." Check it.
9. **p. 38:** "Let `F` be the c-component of `E − Q`." Read this as the component containing `c`,
   and confirm `c ∉ Q`.
10. **p. 38:**
    * "`F` meets only one composant of `I`";
    * "Let `x` be a boundary point of `Q` that belongs to `F`", which is boundary bumping;
    * the existence of `f`, `g` with (1)–(3);
    * "Note that `F`, `f[F]`, and `g[F]` are mutually disjoint. It follows that
      `B ∪ F ∪ f[F] ∪ g[F]` is a triod".

    Record each, and whether it holds as stated.
11. **p. 38, paragraph 4:** "otherwise, `E` would contain an arc [14, Theorem 21, p. 29] and `M`
    would be a simple closed curve [3]". Record that this is set aside, and why.
12. **p. 39, paragraph 9:** "Since `Y ∩ hᵢ[Y] ≠ ∅` and `M` is atriodic and hereditarily
    unicoherent, `hᵢ[Y] ⊂ hᵢk⁻¹[[r,t]] ⊂ E`." The second inclusion is unargued.
13. **p. 39, paragraph 10:** "the closure of `R ∪ T` does not meet an element of `H`. Hence `hᵢ[Y]`
    contains a nonempty open subset of `hᵢ[E]`." Also "`hᵢ[Y]` is an element of
    `{hᵢk⁻¹(u) : 0 ≤ u ≤ 1}`, the minimal admissible decomposition of `hᵢ[E]`". The second needs the
    decomposition to be intrinsic, which is `hagopian75_lemma3_unique`.
14. **p. 39, paragraph 11:** "Using the same argument, one can show that if `Y` is not contained in
    `hᵢ[Y]`, then `Y` has nonvoid interior relative to `E`." Record whether it is the same argument
    applied to `hᵢ⁻¹`.
15. **p. 39:** "Since `Y` is a unicoherent homogeneous plane continuum, it is indecomposable [9,
    Theorem 2]". Record whether Jones 1955 (`doc/sources/jones1955.pdf`) states this, or only
    implies it (item J).

## 4. Deliverables

1. Items A–K.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch155.txt`.
   * Regenerate `axioms.txt`; `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentence quoted.
3. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the ledger entries;
   * the axioms used by each theorem;
   * a reading plan for Hagopian 1976 (`doc/sources/hagopian1976.pdf` will come with batch 156), if
     you have read it. Otherwise give a list of what from this batch it will need: §2's chains that
     *follow* `E`, extensions `R(X, E)`, Lemmas 4–9, Theorem 1.
4. Housekeeping: uploads go to `doc/batches/` and `doc/batches/skeletons/`; sources go to
   `doc/sources/`. Nothing goes at the root.
