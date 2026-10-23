# Commission: batch 187 — Part E, Hagopian 1984 IV: Lemma 13; Lemma 16′; the bridge `J(Z)`

**Go!** This batch runs on top of the batch-186 work. Two files come with it, as separate uploads:

* `COMMISSION-batch187.md`: this text, also pasted into the prompt.
* `Hagopian84C.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian84C.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian84C` at the end of `HPC.lean`. It imports
    `HPC.Hagopian.Hagopian84B`.

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
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1984 IV (batch 187)");
  * `README.md`;
  * `LEDGER.md`: the Hagopian 1984 section;
  * `OPEN.md`;
  * `doc/notes/hagopian84.md`;
  * `Hagopian84B.lean`: delete the commented-out copies of statements proved here, leaving one-line
    pointers.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 186

* **Delivery.** The tarball and manifest worked. This time the project download was current: its
  `axioms.txt` matches the overlay byte for byte. Keep publishing the tarball (§8.4).
* **Copies.** The skeleton, commission and PDF copies are byte-identical.
* **Audit.** `axioms.txt` has 2306 lines (2261 + 45 added, none removed), with `sorryAx` in none.
  The 45 new declarations use only the standard three axioms. In `Hagopian84B.lean` and
  `Hagopian84A.lean`, `sorry` occurs only inside comments.
* **Route.** David has decided that the batches stay on the 1984 route from now on. The 1976 items
  stay as they are; do not report their dependency map again.
* **Your fold proof** (the sweep) is better than my sketch; keep it.
* **Lemma 16.** Your obstruction is right as far as Hagopian's (1) goes. §3 below replaces Lemma 16
  by what Theorem 1 uses of it, with a proof that needs neither the subchain `𝔔` nor (1).

## 1. The plan

`Hagopian84Decomp` follows from a Jones decomposition (`hagopian84Decomp_of_package`). What remains
is the construction of pp. 343–344:
1. the chain `𝒫` (Lemma 13);
2. for each `Z ∈ Ω(𝒫)∖Δ(𝒫)`, the bridge `J(Z)` and its chain `𝒫(Z)`;
3. the cover `𝔅` and a finite subcover;
4. the relation `𝔇` and its disjointness;
5. claims (5) and (6);
6. the fields of `IsJonesDecomp84`.

This batch: Lemma 13 (§2), Lemma 16′ (§3), the bridge (§4), and, if time remains, `𝒫(Z)` and a
reconnaissance of the cover (§5). The arc step (Jones 1975) comes after the construction.

## 2. Lemma 13

Prove `chainLinks84_runsStraight` and `chainLinks84_regular` in your batch-186 shapes, then
`hagopian84_lemma13` (your assembly note in `Hagopian84B.lean`). On your two obstructions:

1. **The positions of `r` and `s` in (3) need no uniform continuity.** Let `Rᵢ = [x₃ᵢ, x₃ᵢ₊₃]`.
   * If `h[k⁻¹(r)]` meets `L i`, a point `h(z) = g(w)` with `z ∈ k⁻¹(r)`, `w ∈ k⁻¹[Rᵢ]` and `g` a
     `δ`-homeomorphism gives `dist(z, w) < 2δ`.
   * If `r < x₃ᵢ₋₁`, then `z ∈ k⁻¹[[0, x₃ᵢ₋₁]]` and `w ∈ k⁻¹[[x₃ᵢ, 1]]`. So
     `dist(z, w) ≥ ρ(k⁻¹[[0, x₃ᵢ₋₁]], k⁻¹[[x₃ᵢ, 1]]) > 2δ`, which is absurd.
   * The other side is the same. Each conclusion is a comparison of a parameter with one `xⱼ`, read
     off from one of the thirteen `½ρ` bounds.
   * The same argument places `s`. The end-set hypotheses of Lemma 3 then follow from
     `2δ < ρ(k⁻¹[[0, x₁]], k⁻¹[[x₂, 1]])` and its mirror.
2. **(4)**: `effros_homogeneous` with `η` the smaller of `μ = ρ(q, L i)` and the room
   `δ − max_v dist(v, h v)` (positive by compactness). Take `p′ ∈ L i` within the Effros `δ′` of
   `p`; this gives `f` with `f(p) = p′`. Then `f ∘ h` is a `δ`-homeomorphism; (3) for it gives
   `fh[k⁻¹(r)] ⊆ L i`, while `f(q) ∉ L i`.
3. **Kinds D and U of the fold** (commission 186 §3.1.4(b)):
   * the continuum `g[k⁻¹[[0, x₃ᵢ₊₃]]]` (kind D), or `g[k⁻¹[[x₃ᵢ₊₃, 1]]]` (kind U);
   * `subset_of_meets_avoids` against `h[k⁻¹[[r, t]]]` (restricted map, Lemma 6);
   * then the distance from `g[k⁻¹(0)]` (resp. `g[k⁻¹(1)]`) to `h[k⁻¹[[r, t]]]`, from item 1.
4. **The choice of `x`.** Upper semicontinuity gives `η > 0` with `k⁻¹[[0, η] ∪ [1 − η, 1]] ⊆ B`.
   Take `x₃ ≤ η`, `x₁₂ ≥ 1 − η`, and `δ` below the distance from that compact set to `M∖B`.

## 3. Lemma 16′ (what Theorem 1 uses of Lemma 16)

**3.1 Where Lemma 16 is used.** Once, on p. 343: "By Lemmas 7 and 16, each element of the
decomposition of `F(Z)` that intersects `⋃𝒫′` is an element of the decomposition of the closure of
a component of `⋃𝒫′`." Prove that sentence instead, in this more general form (skeleton:
`strand_layer_of_extension`).
* `𝒫` is a chain, normal, free and regular.
* `(F, d)` is any type λ continuum whose end layer `d⁻¹(0)` misses `midUnion P`.
* Conclusion: a layer `d⁻¹(u)` through a point `y ∈ midUnion P` is a layer of `Cl H`, where `H` is
  the component through `y`.

For `F(Z)` the hypothesis holds because `d⁻¹(0) = X(Z)` is an end layer of a strand, and those lie
in `P 0∖P 1` or `P 4∖P 3`, outside `midUnion P`. No orientation of `F` against the chain is needed.

An independent reading of the argument below found it correct. It also found the wording slip and
the unstated identification that 3.3 and step 4 now correct, and the simplification used in step 1.

**3.2 Vocabulary.** A *strand* is `Cl H` for a component `H` of `midUnion P`.
* Strand layers meeting `midUnion P` are interior layers: the end layers lie in `P 0∖P 1` and
  `P 4∖P 3`, which miss `midUnion P`.
* A strand layer meeting `P i` lies in `P i` (`layer_subset_link`). One meeting `Bd P i` lies in
  `Bd P i`.
* Every strand meets `P 2` (`exists_interval_in_P2`).
* **Identification** (skeleton: `strand_layer_mem_delta`). For `x ∈ ⋃𝒫∖Cl(P 0 ∪ P 4)`, the layer
  through `x` of the strand through `x` is the member of `Δ(𝒫)` containing `x`.
  * That layer misses `Cl P 0` and `Cl P 4`, by the two facts above.
  * Members of `Δ(𝒫)` are pairwise disjoint or equal (`delta5_partition`).

**3.3 The dichotomy** (from `layers_agree` and `no_arm_at_interior_layer`). Suppose `d⁻¹(u)`
contains a point `y` of `midUnion P`, and `Cl H` is the strand through `y`. Then either `d⁻¹(u)` is
a layer of `Cl H`, or `Cl H ⊆ d⁻¹(u)`.
* Let `Y` be the layer of `Cl H` through `y`. It is interior, and it lies in some `P i` with
  `i ∈ {1, 2, 3}`.
* If `F ∩ Cl H ⊆ Y`, `no_arm_at_interior_layer` with `A := F` gives `F ⊆ Y`. But
  `∅ ≠ d⁻¹(0) ⊆ F` misses `midUnion P ⊇ Y`, so this is impossible.
* Otherwise `F ∩ Cl H` meets two layers of `Cl H`. `layers_agree` (`E := Cl H`, `G := F`) gives
  either `Cl H ⊆ d⁻¹(v)` (then `v = u`, since `y` lies in both) or `d⁻¹(u)` a layer of `Cl H`.

**3.4 The degenerate alternative is impossible** (skeleton:
`not_strand_subset_extension_layer`). Suppose `Cl H ⊆ d⁻¹(u₀)`.
1. Let `T := {u : d⁻¹(u) ∩ P 2 ≠ ∅}`, open by lower semicontinuity (`d` is an open map;
   `lsc_of_minimalAdmissible`).
   * `0 ∉ T`, since `d⁻¹(0)` misses `midUnion P ⊇ P 2`.
   * `u₀ ∈ T`, since every strand meets `P 2`.
   * Let `α := max([0, u₀]∖T)`; that set is compact and contains `0`. Then `α ∉ T`, so `d⁻¹(α)`
     misses `P 2`, and `(α, u₀] ⊆ T`.
2. For `u ∈ (α, u₀]`, apply 3.3 at a point of `d⁻¹(u) ∩ P 2`. Define the two cases by open
   conditions:
   * *thin*: `d⁻¹(u) ∩ Cl P 0 = ∅`, the complement of the compact `d(F ∩ Cl P 0)`;
   * *spanning*: `d⁻¹(u) ∩ P 0 ≠ ∅`, the open set `d(F ∩ P 0)`.

   They are disjoint. They cover `(α, u₀]`:
   * a strand layer through a point of `P 2` lies in `P 2`, which misses `Cl P 0` (normality);
   * a layer containing a strand meets `P 0`.

   `(α, u₀]` is connected and `u₀` is spanning, so every `u` in it is spanning.
3. Take `uₙ ↓ α` in `(α, u₀]`, `pₙ ∈ d⁻¹(uₙ) ∩ P 2`, and `Zₙ ∈ Δ(𝒫)`, the layer through `pₙ` of the
   strand through `pₙ`. In either branch of 3.3, `Zₙ ⊆ d⁻¹(uₙ)`. Also pick `qₙ ∈ d⁻¹(uₙ) ∩ P 0`.
   * Along one subsequence, `pₙ → z ∈ Cl P 2` and `qₙ → q ∈ Cl P 0`.
   * `z ∈ ⋃Δ(𝒫)`: `Cl P 2 ⊆ ⋃𝒫` (freeness: `Bd ⋃𝒫` misses `Cl(midUnion P)`), and
     `z ∉ Cl(P 0 ∪ P 4)` (normality); then `delta5_partition` applies. Let `z ∈ Z ∈ Δ(𝒫)`.
   * By Lemma 14, `Zₙ → Z` in the Hausdorff sense. Since `F` is closed, `Z ⊆ F`, and by the
     continuity of `d`, `Z ⊆ d⁻¹(α)`. Likewise `q ∈ d⁻¹(α)`.
   * `α ≠ 0`, since `d⁻¹(0)` misses `midUnion P ⊇ Z`.
4. Apply 3.3 to `d⁻¹(α)` at a point `w ∈ Z`.
   * If `d⁻¹(α)` contains the strand through `w`, it meets `P 2`, against `α ∉ T`.
   * Otherwise `d⁻¹(α)` is the layer through `w` of the strand through `w`. By the identification
     of 3.2, that layer is `Z`, which misses `Cl P 0`, against `q ∈ d⁻¹(α)`.

Freeness enters only in step 3, through `Cl P 2 ⊆ ⋃𝒫` and `delta5_partition`. Planarity,
homogeneity and atriodicity enter only through the cited lemmas.

**3.5 Hagopian's own proof.** For the record, in the report only (not to formalize): his
contradiction needs only an interval `[t, w]` of layers, each meeting three consecutive links,
whose union misses some link. His (1) asks for more. Say whether this gives a proof of the printed
Lemma 16 once 3.4 is available.

## 4. The bridge `J(Z)` (p. 343)

The text: "For each element `Z` of `Ω(𝒫)∖Δ(𝒫)`, let `K(Z)` be the component of `⋃𝒫′` that contains
`Z`. Let `X(Z)` be the end set of `Cl K(Z)` that is separated from `Z` in `Cl K(Z)` by `P₃`. By
Lemma 11, `Cl ⋃𝔖(X(Z), Cl K(Z))` is an indecomposable subcontinuum of `N`. Thus `⋃𝔖(X(Z), Cl K(Z))`
intersects `P₃∖K(Z)`. Hence there is an element `F(Z)` of `𝔖(X(Z), Cl K(Z))` that intersects
`P₃∖K(Z)`. By Lemmas 7 and 16, … Hence there is an essential subcontinuum `J(Z)` of `F(Z)` that
contains `Z`, misses `Cl P₃`, and has one end set in `K(Z) ∩ (⋃Δ(𝒫))` and the other end set in
`(⋃Δ(𝒫))∖K(Z)`."

Skeleton: `exists_bridge84`. My reading of the unargued steps:
1. **`K(Z)`.** An end layer of a strand lies in `Ω(𝒫)∖Δ(𝒫)` and outside `midUnion P`, so "the
   component of `⋃𝒫′` that contains `Z`" can fail to exist. Read "the component whose closure has
   `Z` as a layer". Record it.
2. **`X(Z)`.** A strand layer meeting `Cl P 0` lies in `Cl P 0` (it meets `P 0` and lies in it, or
   meets `Bd P 0` and lies in it). So `Z ⊆ Cl P 0` or `Z ⊆ Cl P 4`, and `X(Z)` is the end layer on
   the other side. In particular `Z` misses `Cl P 2`.
3. **`F(Z)`.** Apply `hagopian84_lemma11` to `Cl K(Z)` oriented so that `X(Z)` is over `0`.
   * If `extUnion` missed `P 2∖K(Z)`, then `Cl(extUnion) ∩ P 2 ⊆ Cl K(Z)`. That is a nonempty open
     subset of the indecomposable `Cl(extUnion)` inside its proper subcontinuum `Cl K(Z)`
     (`hagopian76_lemma4` makes extensions strict), which is impossible.
   * So some extension `F` meets `P 2∖K(Z)`.
4. **`J(Z)`.** Write `Cl K(Z) = d⁻¹[[0, c₀]]` and `Z = d⁻¹(z₀)`.
   * By freeness `Cl ⋃𝒫′ ⊆ ⋃𝒫`, so `Cl P 2 ⊆ P 1 ∪ P 2 ∪ P 3`.
   * Let `u*` be the least `u > c₀` with `d⁻¹(u) ∩ Cl P 2 ≠ ∅`. It exists because `F` meets
     `P 2∖K(Z)`, the condition is closed, and `d⁻¹(c₀)` misses `Cl P 2`.
   * By §3, `d⁻¹(u*)` is a layer of a strand `Cl H` with `H ≠ K(Z)`, and it lies in `Δ(𝒫)` (it meets
     `Cl P 2`, so it misses `Cl(P 0 ∪ P 4)`).
   * By `translate_run`, the common segment of `F` and `Cl H` extends to the left of `u*`. So the
     layers just left of `u*` are layers of `Cl H` in `Δ(𝒫)` missing `Cl P 2`. Take `b` among them.
   * On the `Cl K(Z)` side, let `m₂ < z₀` be the largest parameter whose layer meets `Cl P 2`. Take
     `a` just above `m₂`.
   * `J(Z) := d⁻¹[[a, b]]`, with the restricted map.
   * Every layer of `J(Z)` meeting `midUnion P` is a strand layer, by §3 and Lemma 6.

## 5. Last, if time remains: `𝒫(Z)` and the cover

1. **`𝒫(Z)`**: Lemma 13 for `J(Z)` with `A := Cl P 2` and `B := ⋃Δ(𝒫)`, which is open and
   contains both end layers of `J(Z)`. Check that `Z ∈ Δ(𝒫(Z))`:
   * `Z` misses `⋃Δ(𝒫) ⊇ Cl(P(Z) 0 ∪ P(Z) 4)`, because `Z ⊆ Cl P 0` or `Z ⊆ Cl P 4`;
   * `Z` is a layer of the closure of the component of `⋃𝒫(Z)′` through it.
2. **The cover** (reconnaissance; report the argument or the obstruction). The text: "Let `𝔅` be the
   collection of open sets `{⋃Δ(𝒫)} ∪ {⋃Δ(𝒫(Z)): Z ∈ Ω(𝒫)∖Δ(𝒫)}`. Since `𝒫` is free and since
   `𝒫(Z)` is free and (3) holds for each element `Z` of `Ω(𝒫)∖Δ(𝒫)`, it follows that `⋃𝔅` is a
   closed open subset of `M`."
   * By (3) and freeness, `⋃𝔅 = ⋃Δ(𝒫) ∪ ⋃_Z ⋃𝒫(Z)`, and each `Bd ⋃𝒫(Z)` lies in `⋃Δ(𝒫)`.
   * The family is uncountable, and I do not see why a limit of points from different `⋃𝒫(Z)`
     lies in `⋃𝔅`. Find the argument, or say exactly what is missing. A possible way around: the
     sets `Z` near a given point of `Cl ⋃Δ(𝒫)` may share one `𝒫(Z)` (Lemma 15 and the continuity
     of `Δ(𝒫)`).

## 6. Order

1. §3: it is independent of §2.
2. §2.
3. §4. It needs §3; it uses Lemma 13 only in §5.
4. §5.

## 7. Places to check (candidate ledger entries)

1. **Lemma 16**: the printed (1) is unargued; Theorem 1 needs only 3.1, proved here without (1).
   Record which printed steps are replaced.
2. **p. 343**: `K(Z)` for end layers (4.1); `X(Z)` (4.2); "Thus `⋃𝔖(X(Z), Cl K(Z))` intersects
   `P₃∖K(Z)`" (4.3); `J(Z)` (4.4).
3. **Lemma 13**: as batch 186, now with proofs.
4. **The cover**: closedness of `⋃𝔅` (§5.2).

## 8. Deliverables

1. **The items of §2–§5.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch187.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
2. **`LEDGER.md`:** a subsection "Hagopian 1984 IV (batch 187)" in the Hagopian 1984 section, with
   the printed sentences quoted.
3. **Notes:** `doc/notes/hagopian84.md` (Lemma 13, Lemma 16′, the bridge, the cover).
4. **Publish the changes, as in batch 186.** At the end of the run:
   * create `doc/batches/batch187-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch187-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `Hagopian84Decomp`;
   * a skeleton proposal for the next step (the cover, `𝔇`, claims (5)–(6), `hagopian84_decomp`).
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
