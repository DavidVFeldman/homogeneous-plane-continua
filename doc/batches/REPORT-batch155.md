Commission read: `doc/batches/COMMISSION-batch155.md` (batch 155 — Part E, Hagopian 1975 I: Lemmas 1–4, the type A′ subcontinuum, interior layers).

# Report, batch 155

**Status: all items A–K proved; nothing open.** Moore's triod theorem (item C) is proved outright,
so no item carries a hypothesis beyond the skeleton's (paragraph 4 of Theorem 1 stays the
hypothesis `hnd`, as the commission directs). Two skeleton statements that are not Hagopian's
sentences are refuted and kept commented out with corrected forms proved. `lake build HPC` succeeds
with `import HPC.Hagopian.Hagopian75` added at the end of `HPC.lean`. The only `sorry`s in
`HPC/Hagopian/` are inside the two commented-out refuted statements. Every new theorem depends only
on `propext`, `Classical.choice` and `Quot.sound`.

**Files** (all under `HPC/Hagopian/`, namespace `HPC.Hagopian`).

| file | content |
|---|---|
| `Hagopian75.lean` | the skeleton items A–K |
| `H75Defs.lean` | the skeleton's definitions (`IsTriodSet`, `IsAdmissibleMap`, `IsTypeA`, `IsTypeA'`, `layer`), verbatim |
| `H75Basic.lean` | admissible maps: preimages of intervals, end layers, `layer_subset_of_meets'`, necessity in Lemma 2, Lemma 3 (type A′) |
| `H75Composants.lean` | item B: Moore 135–139 |
| `H75MooreA.lean`, `H75MooreB.lean` | item C: the interlacing lemma (Moore 76) and Moore's two cases (Moore 73; 79, 78, 76) |
| `H75Triod.lean` | item C: `MooreTriodStatement`, the bridge `isTriodSet_image`, an indecomposable continuum is not a triod |
| `H75Sep.lean` | Moore 22: a non-unicoherent plane continuum separates the plane |
| `H75Lemma1.lean` | item D |
| `H75Kur.lean`, `H75KurScale.lean`, `H75KurMap.lean`, `H75Transfer.lean` | item E, sufficiency: Kuratowski §48 III, IV, VII |
| `H75Thm1A.lean` | item H (paragraphs 1–3) |
| `H75Thm1B.lean` | item I (paragraphs 9–11) |
| `H75Thm1C.lean` | items I (paragraphs 5–8, 12) and K |
| `H75Jones.lean` | item J |
| `H75Counter.lean` | `not_admissible_end_sets`; `arc_of_degenerate_layers'`, `exists_arc_of_degenerate_layers` |
| `H75Sine.lean` | `not_arc_of_degenerate_layers` (the `sin (1/x)` continuum) |

**Statements and shape changes.** A diff of the statements against
`doc/batches/skeletons/Hagopian75.lean` shows these changes, each recorded at the statement:
* `uncountable_composants`: conclusion `¬ (range …).Countable`, since `Set.Uncountable` does not exist
  in Mathlib and the skeleton's line does not elaborate.
* `composant_eq_or_disjoint`: the section variables `[CompactSpace X] [ConnectedSpace X]` are omitted
  (a generalization; they are not used).
* `hagopian75_lemma2`: `hab : a ≠ b` dropped (not used).
* `hagopian75_layer_invariant`: `hr0 : 0 < r` and `ht1 : t < 1` dropped (not used: `ε > 0` already
  forces `k⁻¹[r, t]` to miss the end layers).
* `moore_triod_theorem` is preceded by `open Function in`, so that the skeleton's `Disjoint on T`
  elaborates; the statement is verbatim.
* `admissible_end_sets` and `arc_of_degenerate_layers` are commented out (refuted); corrected forms
  `admissible_end_sets'` (adds the type A′ hypothesis `hk0`, drops `hab`) and
  `arc_of_degenerate_layers'` / `exists_arc_of_degenerate_layers` are proved.
All other statements are verbatim.

**Housekeeping.**
* The commission is `doc/batches/COMMISSION-batch155.md`, the skeleton
  `doc/batches/skeletons/Hagopian75.lean`, the sources `doc/sources/hagopian1975.pdf`,
  `doc/sources/kuratowski2-s48.pdf`, `doc/sources/moore1962-excerpts.pdf`. Nothing new is at the root.
* `Axioms.lean` has the new group "Hagopian 1975 (batch 155)". `axioms.txt` is regenerated (1286
  lines, `sorryAx` in none); the previous version (1221 lines) is kept as
  `doc/batches/audits/axioms-before-batch155.txt`.
* The per-theorem audit is `doc/batches/audits/axioms-batch155.txt` (161 theorems).
* `README.md` and `LEDGER.md` §6 are updated. `OPEN.md` is unchanged, since nothing is left open.

## 1. The items

**A. Definitions; `admissible_quotient_homeomorph` — proved.** The quotient of `E` by the fibre
relation of an admissible map is homeomorphic to `[0, 1]` (the induced bijection is a continuous
map from a compact space to a Hausdorff one). The argument in both directions is written at the
statement. *Map ⇒ decomposition:* the fibres are compact and connected and partition `E`; `k` is a
closed map, so the decomposition is upper semicontinuous; the quotient is `[0, 1]`.
*Decomposition ⇒ map:* compose the quotient map with the homeomorphism onto `[0, 1]`; it is
continuous and onto, and its fibres are the elements. Only the first direction is formalized.

**B. Composants — proved.** `composant_dense` (Moore 135, by boundary bumping,
`HPC.Plane.exists_proper_subcontinuum_meeting`), `composant_eq_or_disjoint` (Moore 138: two proper
subcontinua with a common point have a proper union), `composant_isMeagre` (Moore 136–137: the
composant is covered by countably many proper subcontinua, the components of `x` in `X ∖ b` for `b`
in a countable basis, each with empty interior by `HPC.T13.false_of_interior`),
`uncountable_composants` (Moore 139, Baire).

**C. `moore_triod_theorem` — proved; route: Moore's own two cases.**
* *Separating cores* (Moore 73, `countable_of_separating`): among uncountably many, two triods share
  a small rational ball `Q` meeting both and missing both cores, and a rational point `o` lying in a
  complementary domain of each core not containing `Q`. Those domains then contain each other, so
  are equal, and their frontier lies in both (disjoint) cores — impossible in the connected plane.
* *Non-separating cores* (Moore 79, 78, 76, `countable_of_nonseparating`): each core is enclosed by a
  simple closed polygon whose closed inside misses a chosen point of each leg (`enclose_holds`); a
  countable pigeonhole leaves uncountably many triods with cores inside one polygon `J`; each
  contains a continuum in the closed inside meeting `J` on all three legs (boundary bumping); `J` is
  parametrized by `[0, 2)` (`exists_loop_param`), and two triods whose three boundary points lie in
  the same three disjoint rational parameter intervals contradict the interlacing lemma (`interlace`,
  Moore's Theorem 76, proved from Janiszewski's theorem with no cross-cut).
* The tools are `jordan_curve_theorem`, the enclosing polygon and Janiszewski's theorem of batches
  125–131 and 146–153. The bridge to `HPC.Plane.IsTriod` is `isTriodSet_image` (an injective inducing
  map carries a triod of a compact space to an `IsTriodSet`).

**D. `hagopian75_lemma1` — proved, verbatim, no nondegeneracy hypothesis.**
* First paragraph (`atriodic_of_homogeneous_indecomposable`): `M` is not a triod
  (`not_isTriod_univ_of_indecomposable`), so a triod is proper and lies in a composant; homeomorphisms
  carry it into every composant; Moore 138, 139 and item C.
* Second paragraph (`hereditarilyUnicoherent_of_homogeneous_indecomposable`, also exported as
  `hagopian75_lemma1_hu`; it does not use item C): Moore 22 (`H75Sep.lean`, Eilenberg's argument with
  Borsuk's theorem); the commission's sketch of the "separable" step is correct and is what is
  formalized (`disjoint_components_missing`, `countable_of_pairwiseDisjoint_open`); the density step
  by Baire, Moore 135 and Moore 138. What Hagopian leaves out: the properness of the triod, the
  disjointness of the domains missing `M`, and the Baire and Moore 138 arguments of the density step.

**E. `hagopian75_lemma2`, `admissible_end_sets`, `layer_subset_of_meets`.**
* `hagopian75_lemma2` — **proved** (both directions). Necessity is direct from the layers
  (`not_isIndecomposable_of_typeA'`). Sufficiency follows Kuratowski: the family `D` (§48 III) is a
  chain (`IsDElt.chain`) with no jumps when every subcontinuum with interior is decomposable
  (`IsDElt.exists_between`, VII Theorems 1–2); a countable basis gives a countable dense subfamily
  (`exists_countable_dense_D`), order-isomorphic to `ℚ ∩ (0, 1)` by Cantor's theorem; indexing by it
  gives a scale (`exists_scale`), and `k(y) = inf {q : y ∈ D_q}` is admissible with layers of void
  interior (`scaleMap_spec`, §48 IV and VII Theorems 4–5). So Theorem 3 (the order type of `D`) is
  replaced by the order type of its countable dense part, which is all the monotone map needs.
* `admissible_end_sets` — **refuted** (`not_admissible_end_sets`): on `E = [0, 2]`, `k(x) = max 0
  (x − 1)` is admissible, and `K = [1, 2]` meets both end layers but is not `E`. The first half holds
  for every admissible map (`end_layers`); the corrected `admissible_end_sets'` (with `hk0`) is proved.
  Where Hagopian 1976 uses end sets the map is of type A′, so the correction costs nothing there.
* `layer_subset_of_meets` — **proved**.

**F. `hagopian75_lemma3`, `hagopian75_lemma3_unique`, `arc_of_degenerate_layers`.**
* `hagopian75_lemma3`, `hagopian75_lemma3_unique` — **proved** (`fibre_subset_fibre`,
  `fibre_eq_iff`): any admissible map sends a layer of the type A′ map (a nowhere dense continuum)
  to a point, which is the step of Kuratowski's proof of Theorem 4.
* `arc_of_degenerate_layers` — **refuted** (`not_arc_of_degenerate_layers`): the `sin (1/x)`
  continuum is irreducible between `(1, sin 1)` and `(0, 0)`, the first projection is admissible with
  layers of void interior and degenerate interior layers, but the continuum is not an arc (its end
  layer over `0` is a nondegenerate subcontinuum with void interior). Proved instead:
  `arc_of_degenerate_layers'` (if *every* layer is degenerate, `k` is a homeomorphism onto `[0, 1]`)
  and `exists_arc_of_degenerate_layers` (degenerate interior layers give an arc inside `E`, which is
  what paragraph 4 uses).

**G. `hagopian75_lemma4` — proved, verbatim**, from `effros_homogeneous` with `W` the ball of radius
`δ/2`. Hagopian instead uses Effros's Theorem 2.1 to make `T_x : g ↦ g(x)` an open map of the group
onto `M`, takes `W = T_x[U]` with `U` the homeomorphisms moving points less than `ε/2`, and composes
`h = g f⁻¹`. The repository's Effros theorem is already the uniform statement, so no group topology
is needed.

**H. `hagopian75_no_indecomposable_interior`, `hagopian75_exists_typeA'` — proved, verbatim.**
(`H75Thm1A.lean`.)
* `I ⊆ B` or `I ⊆ C` by hereditary unicoherence and indecomposability; say `I ⊆ B`; `c ∉ I`.
* `F`: any continuum in `E ∖ O` through `c` meeting `cl Q` (boundary bumping) serves for Hagopian's
  `c`-component; `x ∈ F ∩ cl Q ⊆ I`.
* `f`, `g`: by Effros with `ε = min(dist(c, B), dist(q, F))` for a fixed `q ∈ Q`, and, since
  composants of `I` are meagre in `I`, points `f(x)`, `g(x)` of `I` near `x` in two composants of `I`
  other than that of `x` (the one `F` meets). Then (2) holds since `ε ≤ dist(c, B)`, and (3) in the
  form `q ∉ f[F] ∪ g[F]` since `ε ≤ dist(q, F)`. So a different choice from Hagopian's is not needed,
  but `f(x)`, `g(x)` are taken in composants other than that of `x`, as the commission suggests.
* Mutual disjointness: if `F ∩ f[F] ≠ ∅`, then `(F ∪ f[F]) ∩ I` is a continuum (hereditary
  unicoherence) through `x` and `f(x)`, which lie in distinct composants of `I`, so it is `I ∋ q`;
  but `q ∉ F` (as `F ∩ O = ∅`) and `q ∉ f[F]`. Similarly for the other two pairs.
* The triod: core `B`; the three pieces `F ∖ B`, `f[F] ∖ B`, `g[F] ∖ B` are nonempty (they contain
  `c`, `f(c)`, `g(c)`), and pairwise separated because the closure of each lies in its closed source,
  and the sources are disjoint (`isTriod_of_core`). Each source meets `B` (at `x`, `f(x)`, `g(x)`).
  This contradicts Lemma 1.
* `hagopian75_exists_typeA'`: paragraphs 1–2 and Lemma 2.

**I. `hagopian75_layer_invariant`, `hagopian75_layer_homogeneous` — proved.** (`H75Thm1B.lean`,
`H75Thm1C.lean`.) Paragraph 9's second inclusion is proved by a triod argument
(`homeo_image_subset_of_meets`); paragraph 10 by the separation of `h[E ∖ Y]` from the layers
`k⁻¹(u)`, `d < u < e`, and the invariance of relative interior under `h` (instead of the minimal
decomposition of `h[E]`); paragraph 11 is paragraph 10 for `h⁻¹`. Homogeneity of a layer: the
relation "some homeomorphism of `Y` takes `y` to `z`" holds near each point (Effros and the
invariance), so on the connected `Y` it holds everywhere — this is Hagopian's finite chain.

**J. `indecomposable_of_unicoherent_homogeneous` — proved, verbatim**, from `jones55_theorem2'`: the
preimages of the two closed half-circles are subcontinua with disconnected intersection.

**K. `hagopian75_theorem1_of_layer` — proved, verbatim.** The layer `Y` given by `hnd` is a
nondegenerate homogeneous plane continuum (item I), unicoherent by Lemma 1, so indecomposable by
item J.

**Obstruction to Theorem 1 as printed, its Corollary and Theorem 2?** None seen. Theorem 1 as printed
needs only paragraph 4, i.e. Bing 1960 for plane continua (the first half, "`E` would contain an
arc", is `exists_arc_of_degenerate_layers`). Alternatively, once Hagopian 1976 shows that no
subcontinuum of a homogeneous indecomposable plane continuum is decomposable, Theorem 1 and the
Corollary follow without Bing 1960 (Theorem 1's hypothesis becomes impossible; for the Corollary,
every subcontinuum is then indecomposable, so none is hereditarily decomposable). Theorem 2 then needs the
Corollary, Jones 1955 Theorem 2 (`jones55_theorem2'`, with indecomposable nonseparating elements
`jones55_elements_indecomposable'`) and Jones 1955 Theorem 1, which are in the repository. Since 1976
cites only paragraphs 1–3 and 9–11 of Theorem 1, there is no circularity.

## 2. Ledger entries (`LEDGER.md` §6, "Hagopian 1975 I")

Fifteen checks, each with the printed sentence quoted.
1. p. 35, nondegeneracy: needed only for Moore 135–139 and Theorem 1's conclusion; recorded.
2. Lemma 1, "each of its composants contains a triod": properness of the triod unargued; true.
3. Lemma 1, separability and density: both unargued; supplied (disjoint domains, Baire, Moore 138).
4. p. 36, decompositions: the map form agrees (both directions).
5. Lemma 2, Kuratowski Theorem 3: does not state type A′; gap filled by the scale construction.
6. Lemma 3: only the type A′ form proved and used.
7. p. 37: misprint "transfromation"; Effros used in the uniform open-mapping form.
8. "`I` is contained in `E ∩ B` or `E ∩ C`": true.
9. "the c-component of `E − Q`": component of `c`; `c ∉ Q`; true.
10. `F` meets one composant; boundary point `x`; `f`, `g`; disjointness and the triod: all true; the
    last two unargued, supplied.
11. Paragraph 4: set aside (Bing 1960); its first half true; the skeleton's arc form false.
12. Paragraph 9, second inclusion: unargued; true; supplied.
13. Paragraph 10: true; minimal decomposition replaced by interior invariance (uniqueness also
    proved).
14. Paragraph 11: paragraph 10 for `hᵢ⁻¹`.
15. Jones 1955 Theorem 2: implies, does not state, indecomposability; supplied.

No statement of Hagopian is false as printed; no defective proof is added (the count stays at
fourteen). The two refuted statements (`admissible_end_sets`, `arc_of_degenerate_layers`) are
skeleton renderings of Thomas's Theorems 8 and 21, not printed sentences of Hagopian.

## 3. Axioms per theorem

Every one of the 161 new theorems (`doc/batches/audits/axioms-batch155.txt`), and every name in the
group "Hagopian 1975 (batch 155)" of `axioms.txt`, depends on exactly `[propext, Classical.choice,
Quot.sound]`. In particular:

| theorem | axioms |
|---|---|
| `admissible_quotient_homeomorph`, `composant_dense`, `composant_eq_or_disjoint`, `composant_isMeagre`, `uncountable_composants` | propext, Classical.choice, Quot.sound |
| `moore_triod_theorem`, `mooreTriodStatement`, `interlace`, `countable_of_separating`, `countable_of_nonseparating` | propext, Classical.choice, Quot.sound |
| `hagopian75_lemma1`, `hagopian75_lemma1_hu`, `hagopian75_lemma2`, `hagopian75_lemma3`, `hagopian75_lemma3_unique`, `hagopian75_lemma4` | propext, Classical.choice, Quot.sound |
| `admissible_end_sets'`, `layer_subset_of_meets`, `not_admissible_end_sets`, `arc_of_degenerate_layers'`, `exists_arc_of_degenerate_layers`, `not_arc_of_degenerate_layers` | propext, Classical.choice, Quot.sound |
| `hagopian75_no_indecomposable_interior`, `hagopian75_exists_typeA'`, `hagopian75_layer_invariant`, `hagopian75_layer_homogeneous`, `indecomposable_of_unicoherent_homogeneous`, `hagopian75_theorem1_of_layer` | propext, Classical.choice, Quot.sound |

## 4. For Hagopian 1976

Hagopian 1976 is not in hand, so this is a list of what it will need from this batch, by the parts
it cites:
* **Lemma 1** — `hagopian75_lemma1` (atriodic and hereditarily unicoherent), with the composant
  facts `composant_dense`, `composant_eq_or_disjoint`, `composant_isMeagre`,
  `uncountable_composants`, and `moore_triod_theorem`.
* **Lemma 3** — `hagopian75_lemma3` and `hagopian75_lemma3_unique` (the type A′ decomposition is the
  minimal one and is intrinsic, so it is carried by homeomorphisms); `admissible_end_sets'` (end
  layers; note the type A′ hypothesis), `layer_subset_of_meets` (a subcontinuum meeting two layers
  contains those between), `hagopian75_lemma2` (type A′ from decomposability of subcontinua with
  interior).
* **The proof of Lemma 4** — `hagopian75_lemma4` and, for the `ε`–`δ` form, `effros_homogeneous`.
* **Theorem 1, paragraphs 1–3** — `hagopian75_exists_typeA'` (every decomposable subcontinuum
  contains a type A′ continuum), `hagopian75_no_indecomposable_interior`.
* **Theorem 1, paragraphs 9–11** — `hagopian75_layer_invariant` (a homeomorphism near the identity
  that moves an interior layer onto a meeting set maps it onto itself), and its consequence
  `hagopian75_layer_homogeneous`.
* For 1976 §2's chains that *follow* `E` and extensions `R(X, E)`, and for its Lemmas 4–9 and
  Theorem 1: the admissible-map toolkit of `H75Basic.lean` (`isContinuum_img`: preimages of closed
  intervals are continua; `end_layers`), the triod criterion `isTriod_of_core`, hereditary
  unicoherence intersections (`isContinuum_inter_of_HU`), and boundary bumping
  (`exists_continuum_bump_closed`).
