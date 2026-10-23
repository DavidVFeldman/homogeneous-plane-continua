# Commission: batch 99 — closing Bing's Theorem 10 (Duke 1951) with Fugate's counting argument

**Go!** Runs on top of the batch-98 delivery. Two files accompany this commission as separate
uploads, not an archive:

* `COMMISSION-batch99.md` — this text (also pasted into the prompt);
* `LastLink99.lean` — a skeleton, all `sorry`, all work items. Save it as
  `HPC/Plane/LastLink99.lean` and add `import HPC.Plane.LastLink99` at the end of the root
  `HPC.lean`. If `theorem10_1951'` is proved, replace the `sorry` of `theorem10_1951` in
  `HPC/Plane/EndPoints51.lean` by `theorem10_1951' hM D hD hp` (or move the statement) — the one
  permitted edit to an existing file (import order permitting; if it does not, say so and leave
  `theorem10_1951'` as the sorry-free form). Shapes may be adjusted with the change recorded.

The report names the commission read in its first line.

## 0. On batch 98

Audited: the organ is snake-like (zigzag maps, `ε`-map criterion); condition A holds at `p'` on
both sides, against my expectation; the good layer is terminal; the two sides glue in the organ;
my gluing statement refuted twice (two crossing arcs; two organs), the hypotheses having dropped
"`A ∪ B` atriodic and unicoherent", which Fugate's Theorem 1 keeps. Standard axioms, no `sorry`.
Theorem 11 is not refuted and still has no proof in the repository.

## 1. The source: Fugate 1966, Lemma 1 (pp. 461–463)

J. B. Fugate, *Decomposable chainable continua*, Trans. AMS 123 (1966) 460–468, generalizes Bing's
Theorem 10 from a condition-A point to a terminal subcontinuum and supplies the argument Bing
left out. In Bing's orientation (`p` in the first link `f₁ − cl f₂`; `D = (d₁, …, d_m)`;
`M''` a proper subcontinuum through `p` meeting every link of `D`; `F = (f₁, …, f_j)` a chain
covering `M''`, refining `D`, with `p ∈ f₁ − cl f₂`, of least length among such chains), Fugate's
paragraph reads:

[Quotation moved to doc/sources/transcriptions/fugate66.md, §doc/batches/COMMISSION-batch99.md, Lemma 1, proof; batch 204.]

(Fugate writes `E(x,y) ∩ G*(1,t)` for the chain of links `E_i ∩ G*(1,t)`, `x ≤ i ≤ y`, a notation
he defines only when the set `G*(1,t)` meets each common part of adjacent links; `⊕` is
concatenation.)

## 2. Items

**Item 1 (`exists_link_in_between`).** The discrete intermediate value step "`d_r` contains a link
of `F(t, s)`": choose for each `F`-link a `D`-link containing it; consecutive `F`-links meet, so
their chosen `D`-indices differ by at most one; a run of `F`-links from one meeting `d_m` to one
meeting `d₁` passes through every index. Note the chosen index of `f_t` is `m` or `m − 1` (it
meets `d_m`), and of `f_s` is `1` or `2`; so every `r` with `2 ≤ r ≤ m − 1` is attained.

**Item 2 (`lastLink_of_minimal`)** — the claim. Steps and the flags:

1. `f_j` meets `M''`: otherwise `F(1, j − 1)` is a shorter Theorem-10 chain (needs `j ≥ 2`; if
   `j = 1`, `M'' ⊆ f₁ ⊆ d_r` and the claim is about `f₁ ∋ p` — handle: `M'' ∩ d₁ ≠ ∅` gives
   `y ∈ f₁ ∩ d₁ ∩ M''`; is `y ≠ p` available? If `M'' ∩ d₁ = {p}` and `M'' ∩ d_m = {p}` then
   `p ∈ d₁ ∩ d_m` and `m ≤ 2`; for `m = 2` the conclusion may need the alternative form in
   which the point is allowed to be `p` — say what is proved; the downstream use
   `theorem10_1951_of_lastLink` needs `y ≠ p`, so for `m = 2` give Theorem 10 directly: a chain
   of two links covering `M` with `p ∈ d₁`, say, refines itself… — but `p ∉ cl d₂` is not given.
   Treat the small cases explicitly).
2. `f_j ⊆ d_r` with `2 ≤ r ≤ m − 1`, from step 1 and `f_j ∩ M'' ∩ (d₁ ∪ d_m) = ∅`.
3. `f_s`, `f_t` as in the text; `t ≤ s < j` (if `s < t` exchange the roles of `d₁` and `d_m`;
   the skeleton's conclusion is symmetric).
4. Item 1 gives a second `F(t, j)`-link inside `d_r`.
5. **Flag A (the `∩` convention).** `D(y, x) ∩ F*(t, j)` is a chain only if `F*(t, j)` meets
   each `d_i ∩ d_{i+1}`, `x ≤ i < y`. True: `F*(t, s)` is connected (consecutive links meet),
   lies in `D*`, meets `d_m` and `d₁`, hence meets every `d_i ∩ d_{i+1}` (otherwise `D*(1,i)`
   and `D*(i+1,m)` would separate it). Prove this as a lemma.
6. **Flag B (the junction).** The concatenation needs `f_{t−1}` to meet the first link of the
   `D`-part and no other. `f_{t−1} ∩ f_t ≠ ∅` and `f_t` lies in `d_m` or `d_{m−1}`; so the
   `D`-part must start with the `D`-link containing `f_t`: if `f_t ⊆ d_m`, start at `y = m`;
   if `f_t ⊆ d_{m−1}` only, start at `m − 1` — but then is `M'' ∩ F*(t, j) ⊆ D*(x, m−1)`? Points
   of `M'' ∩ d_m ∖ d_{m−1}` are covered by some link of `F`; if that link is `f_i` with
   `i ≥ t`, it lies in `d_m`, so its chosen index is `m` and the run from `t` reaches `m`; so
   `y = m` is needed and the junction is with `d_m ∩ F*(t,j)`, which `f_{t−1}` meets only if
   `f_{t−1} ∩ f_t ∩ d_m ≠ ∅`. Resolve: either show the junction can always be arranged (e.g.
   by taking `t` to be the *last* index whose link lies in `d_m ∪ d_{m−1}` and splitting cases),
   or modify the construction (`F(1, t) ⊕ (D(y, x) ∩ F*(t + 1, j))`, junction via
   `f_t ∩ f_{t+1}`, same issue one step later), or change the count. State precisely what is
   proved; this is the one place where Fugate's text may be incomplete.
7. **Flag C (`p` in the first link only).** If `t ≥ 2` the start `f₁, …, f_{t−1}` is unchanged
   and `p ∉ cl` of the `D`-part links since they lie in `F*(t, j)`. If `t = 1` the new chain is
   `D(y, x) ∩ F*(1, j)` and `p ∈ f₁` may lie in two `D`-links; handle (for instance, `t = 1`
   means `f₁` is the last link meeting `M'' ∩ d_m`, so `M'' ∩ d_m ⊆ f₁`…; or show `t ≥ 2` from
   `p ∉ cl f_i` for `i ≥ 2` and `M'' ∩ d_m ≠ {p}`…). State what is proved.
8. The count: `(t − 1) + (y − x + 1) < (t − 1) + (j − t + 1) = j` because `D(x, y)` has
   `y − x + 1 ≤ m` links, each containing a link of `F(t, j)`, and `d_r` contains two, so
   `j − t + 1 ≥ (y − x + 1) + 1`.
9. The new chain is a Theorem-10 chain for `M''` from `p` refining `D` (refines: `D`-part links
   lie in `d_i`; covers: `M'' ⊆ F*(1, t−1) ∪ (M'' ∩ F*(t, j)) ⊆ … ∪ D*(x, y)`).
10. Contradiction with minimality. Then `f_j ∩ (d₁ ∪ d_m) ∩ M'' ≠ ∅`, and the point is `≠ p`
    when `j ≥ 2` (`p ∉ cl f_j`).

**Item 3 (`exists_minimal_T10Chain`).** `Nat.find`.

**Item 4 (`theorem10_1951'`).** Assembly along Bing's proof as batch 85 set it up (minimal
counterexample `M'` by Zorn for the fixed `D`, every proper subcontinuum through `p` satisfying
the theorem for `D` — condition A passes to subcontinua through `p`; `M''` from
`exists_proper_meeting_all_links` after trimming `D` to the links meeting `M'` — careful: the
trimmed chain is the `D` of items 1–2 and the final `E` must refine the original `D`, which it
does since the trimmed links are links of `D`; the least-length chain; item 2; the surgery
`theorem10_1951_of_lastLink` or its mirror). Then discharge `theorem10_1951` and report the
axiom profiles of `endPoint_of_condA`, `theorem13_1951` (sufficiency) and
`theorem11_1951_of_T10` after the change.

## 3. Deliverables

1. Items 1–4; `#print axioms` in `axioms-batch99.txt`, including the downstream theorems.
2. Report: first line names the commission read; refutations first; flags A–C resolved or
   stated; item 4's edit recorded.
3. Not attempted: `covering_step`, `theorem14` (1948), `theorem3_end`, `exists_tame_chain_near`,
   `isArc_of_separatesPairs`, `exists_degenerate_interior_elt` (false), `theorem11_1951_of_T10'`.

## 4. Next

Fugate's Lemma 1 in its own generality (terminal subcontinua), then Lemma 4 / Theorem 1 (the
gluing with the correct hypotheses); Theorem 11 proper awaits Fugate 1969.
