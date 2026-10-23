Commission read: `COMMISSION-batch100.md` (batch 100: Fugate 1966 — terminal subcontinua, Lemma 1 in general, Theorem 1 (gluing), corollaries; housekeeping). Its skeleton `Fugate66.lean` is saved as `HPC/Plane/Fugate66.lean` (with the shape changes below), the general Lemma 1 and Lemma 2 are in the new file `HPC/Plane/Fugate66Lemma1.lean`, and `import HPC.Plane.Fugate66`, `import HPC.Plane.Fugate66Lemma1` are added at the end of `HPC.lean`.

# Report, batch 100

## Summary

**Refutations first.**

1. **`isFugateTriod_iff_isTriod` is false as transcribed.** The skeleton's `IsFugateTriod` does not
   require the common part `A ∩ B ∩ D` to be connected. Counterexample: the θ-curve, three arcs `A`,
   `B`, `D` with common end points `x`, `y` and disjoint interiors. All pairwise intersections are
   `{x, y}`, a proper subset of each arc, so `IsFugateTriod X`. But `X` is not a triod in Bing's
   sense: if a subcontinuum `N` contains `x` and `y`, every component of `X ∖ N` lies in the interior
   of one arc and each arc contributes at most one; if `N` misses `y` (say), `X ∖ N` is connected
   through `y`. This refutation is **in prose only**; the statement is commented out in the file.
   What holds, formally:
   * `isFugateTriod_of_isTriod` (Bing ⇒ skeleton's Fugate triod);
   * `isTriod_of_isFugateTriod_of_hu` (the converse when `X` is hereditarily unicoherent);
   * with Sorgenfrey's own definition (`IsSorgenfreyTriod`: common part a continuum) the two notions
     coincide outright: `isSorgenfreyTriod_iff_isTriod`.
2. **`isTriod_union_of_three` without hypothesis is false.** Counterexample (prose): the circle as
   the union of the arcs `[0°, 150°]`, `[120°, 270°]`, `[240°, 390°]`. They meet pairwise, none lies
   in the union of the other two, and the circle is not a triod. Sorgenfrey's lemma lives inside a
   hereditarily unicoherent continuum; the **corrected form** (hypothesis: `A ∪ B ∪ D` hereditarily
   unicoherent) is **proved**, via a more general `isTriod_union_of_three_of_core` (hypothesis: the
   union of the pairwise intersections is a continuum).

**Item 0 (housekeeping): done.** `theorem10_1951` and `endPoint_of_condA` (the two `sorry`
declarations) are deleted from `EndPoints51.lean`, whose module docstring changes in one sentence.
In `LastLink99.lean`, `theorem10_1951'` → `theorem10_1951` and `endPoint_of_condA'` →
`endPoint_of_condA`, with the primed names kept as `alias`es. `lake build HPC` succeeds, so no
dependence was missed. `#print axioms` (in `axioms-batch100.txt`): `theorem10_1951`,
`endPoint_of_condA`, `theorem11_1951_of_T10` all use only `propext`, `Classical.choice`,
`Quot.sound`.

**Item 1: proved** (`isTerminalSub_singleton_iff`; triod comparison as above).

**Item 2:** Sorgenfrey's lemma — refuted as stated, proved in corrected form. Sorgenfrey's
irreducibility theorem (`exists_irreducibleBetween_of_atriodic`) — **open**.

**Item 3 (Lemma 3):** (⇐) **proved with no hypothesis on `M`** (`isTerminalSub_of_irreducible`);
(⇒) **proved conditionally** on irreducibility of the subcontinua (`irreducible_of_isTerminalSub`);
the combined `isTerminalSub_iff_irreducible` inherits the `sorry` of Sorgenfrey's theorem.

**Item 4: Lemma 1 in general — proved** (`fugate_lemma1`), with standard axioms only, **without
atriodicity, hereditary unicoherence or Lemma 3** (and so without Sorgenfrey's theorem): only
terminality of `A` in the continuum `M` is used. **Lemma 2 — proved** in the skeleton's form
(`fugate_lemma2`), but see the caveat below: the skeleton's `ContainedExactly` is weaker than the use
Fugate makes of it.

**Item 5:** Theorem 1 — necessity proved; sufficiency **open** (trivial cases and Claim 1 proved).
Corollary 1 — necessity proved; sufficiency **open**. Corollary 2 — **proved from Theorem 1's
sufficiency** (`fugate_cor2_of_theorem1`, `sorry`-free, with Theorem 1's sufficiency as a
hypothesis); `fugate_cor2` itself inherits the open sufficiency. Tautness: `exists_taut_epsChain`
(Barrett's Proposition 1) **proved**; the proof of Lemma 1 does not need it.

## Item 1 details

* `isTerminalSub_singleton_iff`: Definition 4 at `{p}` is condition B. Shape change: the hypothesis
  `hM` (`M` a continuum) is not used and is removed.
* `IsSorgenfreyTriod` (new definition): `IsFugateTriod` plus "`A ∩ B ∩ D` is a continuum".
* `isSorgenfreyTriod_of_isTriod`: from Bing's `X ∖ N = A ∪ B ∪ C` (mutually separated) take the
  continua `N ∪ A`, `N ∪ B`, `N ∪ C`. That `N ∪ A` is connected is a special case of boundary
  bumping, proved directly as `isPreconnected_union_piece`.
* `isTriod_of_isSorgenfreyTriod`: `N = A ∩ B ∩ D`, pieces `A ∖ N`, `B ∖ N`, `D ∖ N`.
* `isTriod_of_isFugateTriod_of_hu`: in a hereditarily unicoherent `X` the common part `A ∩ B` is a
  continuum (it is nonempty, else `X = A ⊔ (B ∪ D)` would be disconnected).

## Item 3 details

* (⇐): if `K`, `L` meet `A` and violate terminality, then `A ∪ K ∪ L` is irreducible from no point of
  `A`: the far point lies in `A ∪ K` or in `A ∪ L`, and that proper subcontinuum would be all of
  `A ∪ K ∪ L`. Neither atriodicity nor hereditary unicoherence is used.
* (⇒): Fugate's argument, with the irreducibility of `A ∪ B` as the hypothesis `hirr` (for every
  nondegenerate subcontinuum of `M`). The degenerate case `A ∪ B = {pt}` is handled separately.
* `isTerminalSub_iff_irreducible`: (⇒) uses `exists_irreducibleBetween_of_atriodic` (open). The
  skeleton's hypothesis `hM` is not used and is removed.

## Item 4 details: Lemma 1 without Lemma 3

The proof is batch 99's induction (`theorem10_aux`) with the terminal subcontinuum `A` in place of
the point `p` (`lemma1_aux`, in Bing's orientation: a point of `A` in the first link only; the
statement is reversed at the end). Four changes:

1. **The surgery** (`surgery_of_sep`, `surgery_of_sep'`). Batch 91's surgery uses condition B at `p`
   only to conclude that a subcontinuum of `M` through `p` missing `y` lies in `K`. That property is
   now the hypothesis `hsep`; the proof is otherwise verbatim. Four hypotheses of batch 91's version
   (`K ⊆ M`, `K` a continuum, `p ∈ K`, `y ∈ K`) turn out to be unused and are dropped. For a terminal
   `A`, `hsep` holds at any `a ∈ A` as soon as `y ∉ A` and `A ⊆ K`: a continuum `C ∋ a` satisfies
   `C ⊆ A ∪ K = K` or `K ⊆ C ∪ A`, and the latter fails at `y`.
2. **The end links** (`t10Chain_of_mem_first`, `t10Chain_of_mem_last`). If some point of `A` lies in
   an end link of `D`, removing a small closed ball about it from the other links and trimming gives
   the required chain at once. (This is Fugate's opening reduction "assume `A ∩ (E_1 ∪ E_m) = ∅`".)
   So in the minimal counterexample `M'`, `A` misses both end links; the point `y` that batch 99's
   `lastLink_of_minimal` puts in `K ∩ (D_0 ∪ D_{m−1})` therefore lies outside `A`.
3. **The composant step** (`exists_proper_superset_meeting_all_links`). Fugate gets a proper
   subcontinuum `N ⊇ A` meeting every link from Lemma 3 (irreducibility of `M'` from `p ∈ A` to
   `q ∉ A`) and the density of a composant. Here instead: for each link, boundary bumping
   (`exists_subcontinuum_meeting_closedBall`, batch 91) gives a subcontinuum `K_i` through a point of
   `A` meeting the link and missing a point outside `A`; by terminality the sets `A ∪ K_i` are
   nested, and the largest one is proper and meets every link. **This removes the dependence on
   Lemma 3, hence on Sorgenfrey's irreducibility theorem, and on atriodicity and hereditary
   unicoherence.**
4. **Minimal chains from a fixed point of `A`.** The least-length chain and the last-link claim are
   batch 99's `exists_minimal_T10Chain` and `lastLink_of_minimal`, applied at a fixed `a ∈ A`; they
   need no change. (Question in item 4: "does `exists_shorter_T10Chain` apply with `A` in the last
   link in place of `p` in the first?" — yes; it is used unchanged, with `p := a`.)

Shape changes of `fugate_lemma1`: hypotheses `hat`, `hhu` removed (unused); ambient space any metric
space. `fugate_lemma1` and `fugate_lemma2` moved to `Fugate66Lemma1.lean` (the surgery needs the
definitions of `Fugate66.lean`); `Fugate66.lean` keeps a pointer.

**Lemma 2 caveat.** The skeleton's `ContainedExactly F A s` says: `A` lies in the final segment
`F(s..n−1)`, not in `F(s'..n−1)` for `s' > s`, and misses the closure of `F(0..s−1)`. This can be
achieved for **any** nonempty compact `A ⊆ M` (`exists_containedExactly`): take the largest such `s`
for the given chain, remove a closed neighbourhood of `A` from the earlier links, and trim. So
`fugate_lemma2` uses terminality only for "`A` is a nonempty compact subset of `M`" (and `hat`,
`hhu` are removed). The definition does not force `A` to occupy the *end* of the chain (e.g. `A`
inside `F(3..5)` of a 10-link chain satisfies it with `s = 3`). If Fugate's Definition 5 / Lemma 2
asks more (for instance that every link of `F(s..n−1)` meets `A`), the definition should be
strengthened; this could not be checked against the scan, which was not available in this session.

## Item 5 details

* `fugate_theorem1_necessity`: batch 96's necessity (the hypotheses on `A`, `B` are not needed).
* `inter_isTerminalSub_of_union` (**Claim 1**): if `A` is hereditarily unicoherent, `A ∪ B` atriodic
  and unicoherent, and `B ⊄ A`, then `A ∩ B` is terminal in `A`. A violation by `K`, `L` gives the
  three continua `K ∪ (A ∩ B)`, `L ∪ (A ∩ B)`, `B`, whose core is
  `(K ∪ (A ∩ B)) ∩ (L ∪ (A ∩ B))` — a continuum because `A` is hereditarily unicoherent — so their
  union is a triod (`isTriod_union_of_three_of_core`). **Gap in Fugate's text named:** Sorgenfrey's
  lemma is cited for three continua in `A ∪ B`, which is only unicoherent; what makes it work is that
  the core lies in the hereditarily unicoherent `A`.
* `fugate_theorem1_sufficiency`: the cases `B ⊆ A`, `A ⊆ B` are trivial; Claim 1 is applied to both
  sides; then `sorry`. **Obstruction:** Fugate's Lemma 4 (fitting the chains `G` of `A` and `H` of `B`
  along `A ∩ B` with properties (1)–(6)) and the two-case construction (Case i `t = m`; Case ii, with
  the index `r`, the sets `D`, Claims 2–3 and Moore's Theorem 44) are not formalized. The commission's
  text of pp. 465–467 is a structural outline only, and the scan was not available in this session,
  so the exact properties (1)–(6) could not be transcribed.
* `fugate_cor1`: necessity proved (`fugate_cor1_necessity`, for any family). Sufficiency is
  **open**: the induction through Theorem 1 needs the partial unions `A_0 ∪ … ∪ A_j` to be
  unicoherent, which does not follow from the unicoherence of the whole union in any way found here
  (it does follow if the whole union is *hereditarily* unicoherent).
* `isAtriodic_of_proper_snakeLike`: a continuum all of whose proper subcontinua are snake-like is
  atriodic. If `M = A ∪ B ∪ D` were a triod (Sorgenfrey form, core `N`), boundary bumping gives a
  subcontinuum `K` with `N ⊊ K ⊊ D`, and `A ∪ B ∪ K` is a proper triod. This is the step of
  Corollary 2's proof that the commission summarises as "follow the text".
* `fugate_cor2_of_theorem1`: with this, Corollary 2 follows from Theorem 1's sufficiency
  (`A ∩ B ≠ ∅` because `M` is connected).
* **Tautness.** `exists_taut_epsChain` (Barrett's Proposition 1) is proved: shrink the links of an
  `ε`-chain whose links meet `M` to open sets with closures inside the links, add small balls to keep
  adjacent links meeting and every link meeting `M`; nonadjacent closures are disjoint compact sets,
  at positive distance (`infDist'_pos`). Lemma 1 as proved does not use tautness; whether the gluing
  needs it was not decided, since the gluing is open.

## Open, with the obstruction

* `exists_irreducibleBetween_of_atriodic` (Sorgenfrey 1944: an atriodic hereditarily unicoherent
  continuum is irreducible). A classical theorem outside the repository. The natural Zorn argument
  over irreducible subcontinua stalls at limits (the closure of a nested union of irreducible
  continua `[a_n, b_n]` need not be irreducible between limit points of `a_n` and `b_n`, so another
  choice of end points is needed), and Sorgenfrey's own argument was not available. It is now needed **only** for
  (⇒) of Lemma 3; Lemma 1 no longer depends on it.
* `fugate_theorem1_sufficiency`, `fugate_cor1` (sufficiency): as above.

## Shape changes recorded

| Declaration | Change |
| --- | --- |
| `isTerminalSub_singleton_iff` | `hM` removed (unused) |
| `isFugateTriod_iff_isTriod` | false; commented out; replaced by `isFugateTriod_of_isTriod`, `isTriod_of_isFugateTriod_of_hu`, `isSorgenfreyTriod_iff_isTriod` |
| `isTriod_union_of_three` | false without hypothesis; hypothesis `hu : IsHereditarilyUnicoherent (A ∪ B ∪ D)` added |
| `isTerminalSub_iff_irreducible` | `hM` removed (unused) |
| `fugate_lemma1` | `hat`, `hhu` removed (unused); moved to `Fugate66Lemma1.lean`; any metric space |
| `fugate_lemma2` | `hat`, `hhu` removed (unused); moved to `Fugate66Lemma1.lean`; any metric space |
| `fugate_theorem1` | split into `fugate_theorem1_necessity` (proved) and `fugate_theorem1_sufficiency` (open) |
| `IsTaut` | marked `noncomputable` (real infimum) |
| definitions, item-1/3 lemmas | the section variable `[CompactSpace S]` is only included where used |

## Files

* `HPC/Plane/Fugate66.lean` — definitions, items 1–3, Theorem 1 (necessity, Claim 1), corollaries,
  tautness.
* `HPC/Plane/Fugate66Lemma1.lean` — the surgery with the separation property, the end-link case, the
  composant step, `lemma1_aux`, `fugate_lemma1`, `exists_containedExactly`, `fugate_lemma2`.
* `HPC/Plane/EndPoints51.lean`, `HPC/Plane/LastLink99.lean` — item 0.
* `Axioms100.lean` → `axioms-batch100.txt`.

## Not attempted (per §3)

`covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
`isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`.
