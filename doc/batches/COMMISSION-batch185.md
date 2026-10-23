# Commission: batch 185 — Part E, Hagopian 1976 XXX: Lemma 7 of 1984; saturation; the case split

**Go!** This batch runs on top of the batch-184 work. Two files come with it, as separate uploads:

* `COMMISSION-batch185.md`: this text, also pasted into the prompt.
* `Hagopian76AC.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76AC.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76AC` at the end of `HPC.lean`. It imports
    `HPC.Hagopian.Hagopian84A`.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure standing for open work, the report gives a note with the two checks:
  1. the hypothesis is not refuted by a short argument from the set-up;
  2. it is not equivalent to the conclusion it is used for, unless the printed argument is a proof
     by contradiction.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXX (batch 185)");
  * `README.md`;
  * `LEDGER.md`: §6 (Hagopian 1976) and the Hagopian 1984 section;
  * `OPEN.md`;
  * `doc/notes/hagopian76-cases.md` and `doc/notes/hagopian84.md`;
  * `Hagopian76AA.lean`, `Hagopian76AB.lean`, `Hagopian84A.lean`: delete the commented-out copies of
    statements proved here, leaving one-line pointers.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 184

* **Delivery.** The tarball and the manifest worked again, PDF included. Keep doing it (§9.4).
* **Copies.** The skeleton, commission and PDF copies are byte-identical.
* **Audit.** `axioms.txt` has 2197 lines (2180 + 17 added, none removed), with `sorryAx` in none.
  The 17 new declarations use only the standard three axioms.

**Accepted, all of it**, including:
* the plane quotient through `fibreSetoid`;
* Hagopian 1975 Theorem 1 with paragraph 4 supplied;
* Lemma 6 without Thomas's Theorem 8;
* the corrections to my dictionary (Lemma 11 is `hagopian76_lemma6_X`; the chains are new).

**One correction to your dictionary.** "There was no `Wset` in the repository" is not right.
`Wset` (`H76Prop1.lean`, the 1976 T5 set `Wₓ`) is your `Wset84` with the conjuncts in the other
order. Keep both. Record the equality (`Wset84 x ε = Wset M ε x` on a plane `M`) as a one-line
lemma.

**This batch** is the 1976 turn of the alternation. Its targets are saturation (2e) and the case
split for `i ≥ 3`. On my reading the first turns on the 1984 Lemma 7, so the batch starts there
(§1–§3). The second does not need it (§5).

## 1. The two-sided extension

Your proposal (report 184 §11): `E` is an essential subcontinuum of a type λ continuum `H` missing
both end sets of `H` (`hagopian84_two_sided` in the skeleton). This is what the 1984 Lemma 7 means
by "By Lemma 4, there is a continuum `H` …". My route, to check:

1. Let `F₁` be an extension of `E` away from `X = k⁻¹(0)`, and `F₂` one away from `Z = k⁻¹(1)`
   (Lemma 4, no maximal element). `E` is an initial segment of each (`hagopian76_initial_segment`).
2. **`F₁ ∩ F₂ = E`.**
   * `F₁ ∩ F₂` is a continuum containing `E` (hereditary unicoherence).
   * Suppose it has a point `p ∈ F₁∖E`. Then it contains the initial segment of `F₁` from `X` to the
     layer of `p`, so it contains points of `F₁∖E` arbitrarily close to `Z` (Lemma 5).
   * These points lie in `F₂∖E`, whose closure meets `E` only in the end layer `X` (as in
     `closure_G_diff_E`). This contradicts `X ∩ Z = ∅`.
3. **`H = F₁ ∪ F₂`, with the glued map** (the layers of `F₂∖E`, then those of `E`, then those of
   `F₁∖E`).
   * The map is admissible: monotone, continuous, onto `[0, 1]`.
   * Its layers have void interior.
4. **`H` is irreducible between a point `a` of the far end set of `F₂` and a point `b` of that of
   `F₁`.** Let `K ⊆ H` be a continuum containing `a` and `b`.
   * `K ∩ F₂` is a continuum containing `a`. `K` must reach `F₁`, and the closure of `F₂∖E` meets
     `E` only in `X`, so `K ∩ F₂` meets `X`. By the irreducibility of `F₂`, `K ⊇ F₂`.
   * Likewise `K ⊇ F₁`.
5. **`E` misses both end sets of `H` and meets more than one layer.**

## 2. Lemma 7 of 1984

> LEMMA 7. *Suppose `F` is a continuum of type λ in `M` such that `E∖F ≠ ∅ ≠ F∖E`. Suppose
> `F ∩ k⁻¹(r) ≠ ∅` for some number `r` (`0 ≤ r ≤ 1`). Then `k⁻¹(r)` is an element of the
> decomposition of `F`.* (p. 336)

* Prove `hagopian84_lemma7`, in the shape of your commented-out block in `Hagopian84A.lean`.
* The proof is printed on pp. 336–337. Its unargued steps are your ledger H84.4: the point `x`; the
  inclusion `k⁻¹(r) ⊂ F`; the point `y`.
* Also state the named `Prop` `Hagopian84Lemma7` (skeleton), so that §4 can be proved conditionally
  if Lemma 7 resists.

## 3. Rigidity and translate runs

**3.1 Rigidity** (`layers_agree`; *shape left to you*). Let `(E, k)` and `(G, d)` be minimal
admissible, and suppose `E ∩ G` meets two layers of `E`. Then on `E ∩ G` the two decompositions
agree. That is, `E ∩ G = k⁻¹[[a, b]] = d⁻¹[[a′, b′]]`, and each layer of the one is a layer of the
other. Expected proof:
* Lemma 7 when neither continuum contains the other;
* Lemma 6 when one contains the other;
* hereditary unicoherence for the connectedness of `E ∩ G`.

Say which degenerate cases need a separate argument (one continuum inside a single layer of the
other), and whether they can occur in §4–§6.

**3.2 Runs** (`translate_run`; *shape left to you*). With `(E, k)`, `(G, d)` as in 3.1, let `h` be a
homeomorphism of `M`, and suppose `G ∩ h[E] = h[k⁻¹[[a, b]]] = d⁻¹[[a′, b′]]` with `a < b`.

**Claim.** Each end of the common segment is either an end of the translate (`a = 0`, `b = 1`) or an
end layer of `G` (`d⁻¹(0)` or `d⁻¹(1)`).

**Proof by atriodicity.** Suppose `0 < a` and the layer `L₀ = h[k⁻¹(a)] = d⁻¹(a′)` is not an end
layer of `G`.
* Then `G ∪ h[E]` minus `L₀` has three nonempty pieces:
  * the common segment beyond `L₀`;
  * the part of `G` on the other side of `L₀`;
  * `h[k⁻¹[[0, a))]`.
* These pieces are mutually separated, since the closures of the last two meet only inside `L₀`.
* So `G ∪ h[E]` is a triod with core `L₀`.

**3.3 Consequence for Hagopian's `F`, to state and check.** Let `C` be a crossing component of
`F ∩ π⁻¹[D]`.
* By `strand_lemma`, `Cl C ⊆ h[E]` for the translate through a point of `C` over the middle.
* By 3.1–3.2, `F ∩ h[E]` is a common segment containing `C`. Along `h[E]` it runs from `C` to within
  `2/n` of a translate end (by S0, outside `D`'s abscissae), or to `F`'s end layer `d⁻¹(1)`.
* So, except possibly at `d⁻¹(1)`, `F` leaves `D` along the same translate. It crosses each side
  segment within the window of `S0` (`|abscissa − parameter| < 2/n`).

This is what Bing's arcs have and Hagopian's strands lacked (report 183 §3). §6 uses it.

## 4. Saturation (2e)

Target: `innerComponentsCross_hagopian`, or `innerComponentsCross_hagopian_of_lemma7` from the named
`Prop`. Let `y = h(e)` lie over `(3/22 + 8/n, 19/22 − 8/n)`, and let `W` be its component in
`F ∩ O`. Write `K⁻ = F ∩ h[k⁻¹[[0, k(e)]]]` and `K⁺ = F ∩ h[k⁻¹[[k(e), 1]]]`.

**4.1 Steps 4–5 of `noncrossing_half_in_O`.** If `K⁻ ⊄ O` and `K⁺ ⊄ O`, then `W` is a crossing
piece.
1. `half_bump_side` gives `q⁻ = h(z) ∈ K⁻` in the closure of the component of `K⁻ ∩ O` through
   `y`, with `π(q⁻) = F(w)` and `w.1 ∈ {3/22, 19/22}`.
2. S0 (`StrandConst.fine`) gives `|k(z) − w.1| < 2/n`. Since `k(z) ≤ k(e) < 19/22 − 8/n`, we get
   `w.1 = 3/22`. Likewise `q⁺` lies over `19/22`.
3. Both components lie in `W`, so `Cl W` meets both closed side segments.
4. The heights lie strictly inside, as in `side_point_open`: not on the bottom edge, by
   `closure_G_diff_E`; not on `I₂`, by T7. The other fields of `IsCrossingPiece` follow as in
   `isCrossingPiece_of_crossingComponent`.

**4.2 The tip, by Lemma 7.** Suppose `K⁻ ⊆ O`. My argument, to check:
1. **The tip.** `τ = min {k(e′) : k(e′) ≤ k(e), h(e′) ∈ F}` is attained at some `e₀`, by
   compactness. `h(e₀) ∈ K⁻ ⊆ O`, so `h(e₀)` lies over `D`.
2. **The tip meets the end layer.** `tip_meets_end_layer` with `b = k(e)` gives `e′` with
   `k(e′) = τ` and `h(e′) ∈ d⁻¹(1)`.
3. **`h[E] ⊄ F`.** Otherwise `h[k⁻¹(0)] ⊆ K⁻ ⊆ O`. But by S0 a point of `h[k⁻¹(0)]` over `D` would
   have abscissa `< 2/n < 3/22`.
4. **`F ⊄ h[E]`.** Otherwise a point `z ∈ k⁻¹(0) ⊆ E ⊆ F` is `h(z′)` with `k(z′) < 2/n` (S0 at
   `π(z) = F(0, 0)`). Then `z ∈ K⁻ ⊆ O`, while `E ∩ O = ∅`.
5. **The layers agree.** Lemma 7, with `h[E]` (map `k ∘ h⁻¹`) for `E` and Hagopian's `F` for `F`,
   gives `h[k⁻¹(τ)] = d⁻¹(u)` for some `u`. By step 2, `u = 1`.
6. **The contradiction.** `d⁻¹(1) = h[k⁻¹(τ)] ⊆ K⁻ ⊆ O`, against 3a
   (`T12Data.end_layer_not_subset`).
7. **`K⁺ ⊆ O`** is the mirror, with `tip_meets_end_layer_mirror` (or its `_rel` form).

**4.3 Assembly.** `innerComponentsCross_hagopian_of_lemma7`, and, if §2 is proved,
`innerComponentsCross_hagopian`. Give the case tree in the report.
* If 4.2 holds, the points `zⱼ`, the chunk, the edge case `F ∩ hⱼ[E] ⊆ Tⱼ` and `τ₁ = 1` (batches
  179–183) are no longer needed. Say whether that is so.
* Leave the earlier tip results as they are.

## 5. The case split for `i ≥ 3` (`BlockLayersMeetSides3`)

My route does not use Lemma 7; check it. Let `3 ≤ i ≤ m` with tight blocks.
1. **The block ends are ends of crossing intervals.**
   * By tightness, `x₂ᵢ₋₁` lies in a member `[u, v]` of `I`. That member lies inside the block, so
     `u = x₂ᵢ₋₁`.
   * Likewise `x₂ᵢ₋₂` is the right end `v′` of a member `[u′, v′]` inside `J`.
2. **Take `u`.** Let `C` be a crossing component with irreducible interval `[u, v]`. Then `Cl C`
   meets `d⁻¹(u)` (`exists_irreducibleInterval`).
3. **`d⁻¹(u) ⊄ O`.** Otherwise:
   * `d⁻¹(u)` is connected, meets `Cl C`, and lies in `O`. `C` is closed in `O`, so `d⁻¹(u) ⊆ C`.
   * By upper semicontinuity, `d⁻¹[[u − η, u]] ⊆ O` for small `η`. That set is a continuum meeting
     `C`, so it lies in `C`.
   * This is against `C ⊆ d⁻¹[[u, v]]`. Note `u > x₂ > 0`.
4. **So `d⁻¹(u)` meets `Fr O`.**
   * If `d⁻¹(u)` meets `O`, it does so because it is connected and not inside `O`.
   * If not, the point of `Cl C ∩ d⁻¹(u)` lies in `Cl O∖O`.
5. **The frontier point is over a side segment.** `Fr O ⊆ π⁻¹[Fr D]`.
   * Not over `I₂` (T7).
   * Not over the bottom edge: that would put the point in `E = d⁻¹[[0, x₂]]`, while `u > x₂`.
   * So `d⁻¹(u)` meets a closed side segment.
6. **The same for `v′ = x₂ᵢ₋₂`**, using `d⁻¹[[v′, v′ + η]]`, with `x₂ < v′ < 1`.

This also locates `d⁻¹(x₃)` at the last step (notes E3: "not located by anything proved"). If the
route holds, prove `blockLayersMeetSides3`. Also record which side each layer meets, for §6.

## 6. Last, if time remains: "between" with runs

Re-examine the obstruction of report 183 §3 with §3.3: a strand that only touches the side segment,
with `F` having no points outside `D` near its end.
* By 3.3, `F` leaves `D` along the strand's translate within the `S0` window, except possibly at
  `d⁻¹(1)`.
* Apply 3.1–3.2 also to `L` (type λ, `L ∩ F = ∅`) against the translate of `Cᵢ`.
* Prove `case1_between_bing` from this, or state precisely what remains.

## 7. Order

1. §1 → §2 → §3.
2. §4.
3. §5. It is independent; do it early if §1–§2 stall.
4. §6.
5. **Theorem 1.** Give the strongest conditional form, `hagopian76_theorem1_of_cases4`: from
   `StepFrame`, `LastStepClaims`, `Case1ClaimsE24`, `Case2ClaimsE24` (and `Hagopian84Lemma7`, if
   §2 is open), with `hICC` and `BlockLayersMeetSides3` discharged.

## 8. Places to check (candidate ledger entries)

1. **The 1984 Lemma 7 (p. 336) and Lemma 4 as used there.** The two-sided extension. Lemma 2
   applied to `F ∪ J` (your H84.2).
2. **A.23 of my ledger, "The end layer of `F` over `D`"** (open since batch 178). If §4.2 holds, it
   is closed by a lemma Hagopian proved eight years later, in a different paper. Record which steps
   of the 1976 text this replaces.
3. **p. 348, "The proof now breaks down into two cases".** If §5 holds, the presupposition is true
   for `i ≥ 3` and false only at `i = 2` (`blockLayersMeetSides_false`).
4. **p. 348, "between"** (§6): whether runs supply Bing's "the arcs end on the side lines".

## 9. Deliverables

1. **The items of §1–§7.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch185.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
2. **`LEDGER.md`:** subsections for this batch in §6 and in the Hagopian 1984 section, with the
   printed sentences quoted.
3. **Notes:** `doc/notes/hagopian76-cases.md` (runs, the case split, the effect on E2–E3) and
   `doc/notes/hagopian84.md` (Lemma 7, the two-sided extension).
4. **Publish the changes, as in batch 184.** At the end of the run:
   * create `doc/batches/batch185-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch185-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency maps of Theorem 1, for both routes;
   * a skeleton proposal for what remains.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
