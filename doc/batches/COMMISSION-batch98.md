# Commission: batch 98 — the Cantor organ as a test of Theorem 11 (Duke 1951)

**Go!** Runs on top of the batch-97 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch98.md` — this text (also pasted into the prompt);
* `Organ98.lean` — a skeleton, all `sorry`, all work items. Save it as `HPC/Plane/Organ98.lean`
  and add `import HPC.Plane.Organ98` at the end of the root `HPC.lean`. No existing file is to be
  edited. Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 97

Audited: Fort's theorem for the element map; a continuity point outside the end elements; and the
Cantor organ — `BingS`, elements = layers, every element nondegenerate, interior layers not end
elements, Hausdorff continuity at good parameters; `theorem11_hdeg_refuted`. Standard axioms.
`exists_degenerate_interior_elt` in `Theorem11.lean` is now known to be false and stays as a
`sorry` to be deleted at the pruning pass; `theorem11_1951_of_T10` is vacuous in universe 0.

Consequence: Bing's proof of Theorem 11 is incomplete beyond repair by a choice of `g'`. In the
organ every interior element is nondegenerate, and batch 96 showed that the displayed chain
`H'·h₁, …, (H'·h_m) + N + (K'·k₁), …` cannot be formed when `g'` is nondegenerate. Theorem 11 is
cited by Nadler (p. 232) on Bing's proof alone; an independent route is Fugate, *Decomposable
chainable continua*, Trans. AMS 123 (1966), Corollary 2, which I do not yet have. So the organ is
the test: if it is not snake-like, Theorem 11 is false.

## 1. Item 1: `organ_isSnakeLike` — prove or refute

The organ's structure (batch 97): lexicographic order on (layer, position in layer); subcontinua
order-convex; order-convex sets connected; layers are strands (non-dyadic `t`) or V's (dyadic
`t`); odd-generation gaps glued at the top, even-generation gaps at the bottom.

A chain of mesh `ε` would have to run through the strands in the order of `F`, entering a strand
at the end where it is glued to its predecessor and leaving it at the other end — so the chain
runs *up* one strand and *down* the next, and the alternation of the gluings is what makes this
consistent. At the level of a finite approximation (digits up to generation `n`, strands of
length 1 and width `3^{-n}`-ish in the embedding): the `2^n` strands of generation `n`, joined
alternately at top and bottom, form a zigzag arc; the organ is the limit of such zigzags as `n`
grows, and each zigzag has a chain of mesh `ε` once its strands are thinner than `ε` — but the
*same* chain must also cover the deeper strands accumulating on each strand of generation `n`,
and those approach from one side only. Decide: either construct the chains (the zigzag of
generation `n` with links of height `< ε` and width covering the whole cylinder over a
generation-`n` interval of the Cantor set), or exhibit the obstruction (a triod-free continuum
that is not chainable would have positive span; show the organ has positive span, or that no
`ε`-chain exists for some `ε`).

## 2. Item 2: Bing's nondegenerate branch on the organ

With `g'` the good layer `layer (lam goodC)` (a single strand, an arc) and `p'` its top point
`pt goodC 1`:

* `organ_condA_layer`: `p'` satisfies condition A for `M = g'` (an end point of an arc does).
* `organ_condA_H_or_K`: Bing's "`p'` satisfies condition A for `M` equal to either `H` or `K`",
  with `H = F⁻¹[0, lam goodC]`, `K = F⁻¹[lam goodC, 1]`. For each side decide whether condition A
  holds at `p'`; prove the true side(s) and refute the false one(s) (the report, not the skeleton,
  carries any refutation). Expectation: on the side whose strands near `g'` are glued to `g'`'s
  neighbours at the *bottom*, the top point `p'` is an end point in the order and condition A
  should hold; on the other side it should fail (a subcontinuum through `p'` running into the
  neighbouring strands and up them is not irreducible from `p'`). Record which.

## 3. Item 3: gluing along a nondegenerate terminal layer

Define `IsTerminalIn M T` (every subcontinuum of `M` meeting `T` lies in `T` or contains `T`;
batch 96's derived fact, as a definition).

* `organ_layer_terminal`: the good layer is terminal in both sides (order-convexity).
* `isSnakeLike_union_of_terminal` — **the question**: if `H`, `K` are snake-like, `H ∩ K = T` is
  terminal in both, and `H ∪ K` is a continuum, is `H ∪ K` snake-like? This is the lemma a
  repaired Theorem 11 would need in place of Bing's amalgamation at a point. Prove, or refute
  (a refutation would be two chainable continua whose chains traverse `T` in incompatible ways —
  the organ with a *single* strand as `T` is a candidate for both outcomes: if item 1 proves
  the organ snake-like, the two sides glue; if item 1 refutes it, the two sides `H`, `K` of the
  good layer, if they are themselves snake-like, refute the gluing lemma). State what is proved;
  if open, the obstruction.

## 4. Deliverables

1. Items 1–3; `#print axioms` in `axioms-batch98.txt`.
2. Report: first line names the commission read; refutations first; item 1 with the chains or the
   obstruction; item 2 side by side; item 3.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, the last-link claim of
   `theorem10_1951`, `exists_tame_chain_near`, `isArc_of_separatesPairs`,
   `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`.

## 5. Next

Depends on item 1. If the organ is snake-like: Theorem 11 needs a new proof (Fugate's, or a
gluing lemma); if not: Theorem 11 is refuted and the record is complete.
