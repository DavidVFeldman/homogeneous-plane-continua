# Commission: batch 188 — Part E, Hagopian 1984 V: `𝔇`; claims (5)–(6); `hagopian84_decomp`

**Go!** This batch runs on top of the batch-187 work. Two files come with it, as separate uploads:

* `COMMISSION-batch188.md`: this text, also pasted into the prompt.
* `Hagopian84D.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian84D.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian84D` at the end of `HPC.lean`. It imports
    `HPC.Hagopian.Hagopian84C`.

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
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1984 V (batch 188)");
  * `README.md`;
  * `LEDGER.md`: the Hagopian 1984 section;
  * `OPEN.md`;
  * `doc/notes/hagopian84.md`;
  * `Hagopian84A.lean`: replace the commented-out copies of statements proved by now (Lemmas 13
    and 16, `hagopian84_quotient_arc`, `hagopian84_decomp`, `hagopian76_theorem1_jones`) by
    one-line pointers;
  * `Hagopian84C.lean`: the header and the §5 comment only (§5.8 below).

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 187

* **Delivery.** The project download was stale again: its `axioms.txt` is the batch-186 one (2306
  lines). Your tarball and manifest carried the work; the overlay gives 2392 lines. Keep
  publishing both (§8.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2392 lines (2306 + 86 added, none removed), with `sorryAx` in none.
  The 86 new declarations use only the standard three axioms. In the eight new files `sorry` occurs
  in no declaration.
* **Every item proved**, including both §5 items. The finite cover without the closedness of `⋃𝔅`
  is the right move.
* **One correction to your §0.** The printed sentence "`⋃𝔅` is a closed open subset of `M`" is not
  open as a statement. For the same choice of chains, your finite cover gives `⋃𝔅 = M`, which is
  closed. What is unargued in print is only the reason given (freeness and (3)). State the
  corollary (§5.8) and move the `OPEN.md` entry to "printed reason unargued; statement proved".
* **Omission 3** (`Hagopian84A.lean` not editable): it is on the list now.
* **The end-set positions of `J(Z)`**: nothing below needs them either.

## 1. The plan

What remains of `Hagopian84Decomp` is the end of p. 343 and p. 344:
1. the decomposition `𝔇 = ⋃ᵢ Δ(𝒫(Zᵢ))` (with `𝒫(Z₀) = 𝒫`) and its disjointness;
2. claims (5) and (6);
3. the fields of `IsJonesDecomp84`, then `hagopian84_decomp` by `hagopian84Decomp_of_package`;
4. `hagopian76_theorem1_jones`: Theorem 1 of 1976 from `NoArcIndecHomPlane` alone.

All of it rests on one transfer lemma (§2), which replaces Hagopian's "by (2), (3), and Lemma 7"
and "by (3) and Lemma 7" on p. 344. After this batch the arc step (Jones 1975) is the last open
input of Theorem 1 of 1976 on this route.

## 2. The transfer lemma (skeleton: `omega_layer_of_mem_mid`, `omega_mem_delta_of_mem_mid`)

**Statement.**
* `𝒫` is a normal regular chain.
* `Q` is a free normal regular chain with `⋃Q ⊆ M∖Cl P 2` (Hagopian's (2)).
* `Z ∈ Ω(𝒫)`, and `z ∈ Z ∩ midUnion Q`.

Then `Z` is the layer through `z` of the strand of `Q` through `z`. If also `z ∉ Cl(Q 0 ∪ Q 4)`,
then `Z ∈ Δ(Q)`.

**Proof.**
1. `Z` is a layer of a strand `G` of `𝒫`. By regularity `G` has a map `c` running straight through
   `𝒫`, and `Z = c⁻¹(r)` for some `r` (`exists_layer_eq_of_minimal`).
2. `G` meets `P 2` (`strand_meets_P2_P0`). Take `p ∈ G ∩ P 2` and `s = c(p)`. Then `c⁻¹(s) ⊆ P 2`
   (`layer_subset_link`).
3. `z ∈ ⋃Q`, which misses `Cl P 2 ⊇ c⁻¹(s)`. So `z ∉ c⁻¹(s)`, and `s ≠ r`.
4. Let `F = c⁻¹[[min(r, s), max(r, s)]]`, with the map of `minimalAdmissible_restrict`. Compose it
   with `unitInterval.symm` when `r < s` (`IsMinimalAdmissible.symm_comp`, `layer_symm_comp`).
   The resulting map `d` has `d⁻¹(0) = c⁻¹(s)` and `d⁻¹(1) = c⁻¹(r) = Z`.
5. `d⁻¹(0) ⊆ P 2` misses `midUnion Q ⊆ ⋃Q`. Lemma 16′ for `Q` (`strand_layer_of_extension`, with
   `u = 1` and `y = z`) gives the first claim.
6. The second claim then follows from `strand_layer_mem_delta` for `Q`.

The proof uses (2) and not (3).

## 3. The data, `𝔇`, disjointness

**3.1 The data** (skeleton: `CoverData84`, `exists_coverData84`). The structure records:
* `𝒫`, free, normal and regular;
* a finite set `S` of members `Zᵢ` of `Ω(𝒫)∖Δ(𝒫)`;
* for each `Zᵢ`, its chain `𝒫(Zᵢ)` with the properties of `hagopian84_cover`;
* the cover.

`exists_coverData84` builds it in three steps:
1. a type λ continuum `E`, from a decomposable subcontinuum by `hagopian75_exists_typeA'`, as at
   the start of `exists_thm1Setup`;
2. Lemma 13 with `ε = 1`, `A = ∅`, `B = M`;
3. `hagopian84_cover`.

**3.2 `𝔇`** (skeleton: `CoverData84.members`) is `Δ(𝒫) ∪ ⋃_{Z ∈ S} Δ(𝒫(Z))` ("For convenience we
define `𝒫(Z₀)` to be `𝒫`"; "Let `𝔇` be `⋃{Δ(𝒫(Zᵢ)): 0 ≤ i ≤ n}`").

**3.3 Every point lies in a member**: the cover (`mem_sUnion`).

**3.4 Disjointness** (skeleton: `CoverData84.members_disjoint`). The text (pp. 343–344): "Let `A`
and `B` be intersecting elements of `𝔇`. If `A ∪ B` intersects `⋃Δ(𝒫)`, then, by (2), (3), and
Lemma 7, `A = B`. Hence we assume that `A ∪ B` misses `⋃Δ(𝒫)`. … Since `A ∪ B` misses `⋃Δ(𝒫)`, it
follows from (3) that `A ∪ B` misses both end sets of `Cl I` and both end sets of `Cl J`. Thus, by
Lemma 3, `A = B`."

Let `A` and `B` be members with a common point `x`. There are three cases.
* **(a) `A, B ∈ Δ(𝒫)`.** Use `delta5_partition`.
* **(b) `A ∈ Δ(𝒫(Zᵢ))` and `B ∈ Δ(𝒫)`.**
  1. `x ∈ ⋃Δ(𝒫(Zᵢ)) = ⋃𝒫(Zᵢ)∖Cl(P(Zᵢ) 0 ∪ P(Zᵢ) 4)`. So `x` lies in `midUnion 𝒫(Zᵢ)`, outside
     `Cl(P(Zᵢ) 0 ∪ P(Zᵢ) 4)`.
  2. §2 with `Z := B` gives `B ∈ Δ(𝒫(Zᵢ))`.
  3. `delta5_partition` for `𝒫(Zᵢ)` gives `A = B`.
* **(c) `A ∈ Δ(𝒫(Zᵢ))` and `B ∈ Δ(𝒫(Zⱼ))`.**
  * *If `A` or `B` meets a member `Y` of `Δ(𝒫)`:* (b) makes that one equal to `Y`. Then the other
    meets `Y`, and (b) again makes it equal to `Y`.
  * *Otherwise* use Hagopian's argument: `hagopian76_lemma3` with `h` the identity, `E` the strand
    of `A` and `F` the strand of `B`.
    * Take the maps from `delta_regular_rep` (`H84Lemma1415.lean`). They run straight, and they
      give `A` and `B` as interior layers (`0 < s < 1`) in one step.
    * The end layers of a map running straight lie in `R 0 ∖ R 1` and `R 4 ∖ R 3`. For an arbitrary
      minimal admissible map of the strand this is not available, so use these maps. The end layers
      then lie in `Cl(P(Z) 0 ∪ P(Z) 4) ⊆ ⋃Δ(𝒫)` by (3), and `A ∪ B` misses `⋃Δ(𝒫)`.

**My reading of Hagopian's first case (candidate ledger entry).** An independent check of this
commission agrees with it and narrows it. Lemma 7 needs `E∖F ≠ ∅ ≠ F∖E`. Take the strand `S_A` of
`𝒫(Zᵢ)`, the member `Y ∈ Δ(𝒫)` through the common point, and the strand `S_Y` of `Y`.
* Every strand of `𝒫` meets `P₃`, and by (2) `S_A` misses `P₃`. So `S_Y ⊄ S_A`.
* `S_A ⊄ S_Y` is not argued. If `S_A ⊆ S_Y` without lying in one layer, `layers_agree`
  (`E := S_Y`, `G := S_A`) gives `A = Y` with no need for Lemma 7. So the only case the text leaves
  open is `S_A ⊆ Y`.
* (3) does not exclude `S_A ⊆ Y`: it only puts the end links of `𝒫(Zᵢ)` inside `⋃Δ(𝒫)`.
* Hagopian's "first note" on p. 344 would exclude it: "each component of `⋃Δ𝒫(Zᵢ)` misses `P₃`
  and intersects `M∖⋃𝒫′`". The component containing `A` lies in `S_A`, and `Y ⊆ ⋃𝒫′`. But that note
  is itself unargued. It seems to need the end links of `𝒫(Zᵢ)` in different components of
  `⋃𝒫′`, which Lemma 13 and (3) do not give.
* §2 covers `S_A ⊆ Y` through Lemma 16′.

Record this in the ledger. Say whether you see an argument for the "first note".

**3.5 The relation** (skeleton: `CoverData84.setoid`, `CoverData84.cls_eq`). `x ~ y` if and only if
some member contains both. It is reflexive by 3.3 and transitive by 3.4. The class of `x` is the
member through `x`.

## 4. Claims (5) and (6)

The text: "Since `𝒫` is a free regular chain, it follows from (3) and Lemma 7 that (5) for each
integer `i` (`0 ≤ i ≤ n`), `Ω(𝒫(Zᵢ)) ⊂ 𝔇`. By Lemma 15, for each integer `i` (`0 ≤ i ≤ n`) there
is a positive number `εᵢ` such that if `Z ∈ Δ(𝒫(Zᵢ))` and `h` is an `εᵢ`-homeomorphism of `M` onto
`M`, then `h[Z] ∈ Ω(𝒫(Zᵢ))`. Let `δ` be the minimum of `{εᵢ: 0 ≤ i ≤ n}`. It follows from (5) that
(6) if `Z ∈ 𝔇` and `h` is a δ-homeomorphism of `M` onto `M`, then `h[Z] ∈ 𝔇`."

**4.1 (5) for `i = 0`, in full** (skeleton: `CoverData84.omega_subset_members`). Let
`Z ∈ Ω(𝒫)∖Δ(𝒫)`.
1. `Z ⊆ Cl P 0` or `Z ⊆ Cl P 4` (`omega_not_delta_side`). So `Z` misses `⋃Δ(𝒫)`.
2. Take a point `z ∈ Z`. By the cover, `z` lies in some `A ∈ Δ(𝒫(Zᵢ))`.
3. §2 gives `Z ∈ Δ(𝒫(Zᵢ))`.

**4.2 (5) for `i ≥ 1`, for members inside `⋃𝒫(Zᵢ)′`** (skeleton:
`CoverData84.omega_mem_members`). Let `W ∈ Ω(Q)` with `Q = 𝒫(Zᵢ)` and `W ⊆ midUnion Q`. If
`W ∈ Δ(Q)`, we are done. Otherwise:
1. `W ⊆ Cl Q 0` or `W ⊆ Cl Q 4` (`omega_not_delta_side` for `Q`). So `W ⊆ ⋃Δ(𝒫)` by (3).
2. Take `w ∈ W`, and `Y ∈ Δ(𝒫)` through `w`. By §2, `Y` is the layer through `w` of the strand of
   `Q` through `w`.
3. So is `W`. `W` is a layer of `Cl K′` for a component `K′` of `midUnion Q`. `K′ ∪ W` lies
   between `K′` and `Cl K′` and inside `midUnion Q`. So `W ⊆ K′`, and `K′` is the component through
   `w` (`connectedComponentIn_eq`).
   * This is the argument of `delta_subset_component`, but that lemma cannot be applied as stated.
     Its hypothesis `Disjoint Z (closure (P 0 ∪ P 4))` is exactly what fails here.
   * Reuse its last lines with `W ⊆ midUnion Q` in place of its `hZU`, or generalize it to assume
     `Z ⊆ midUnion P`.
4. `layer_eq_of_common_point` (with `hGG'` from `congrArg closure`) gives `W = Y ∈ Δ(𝒫)`.

**Points of a strand.** Wherever a point of a strand `Cl K` in `midUnion Q` is used, choose it in
`K` itself. `M` is not locally connected, so `Cl K ∩ midUnion Q` can meet other components.

**The printed (5) holds in full (optional, not needed for (6)).** The independent check gave an
argument for members outside `⋃𝒫(Zᵢ)′`. Formalize it only if time remains; otherwise record it in
the report.
1. Let `W` be such a layer of a strand `S = Cl K` of `Q`. By `layer_subset_link` and connectedness,
   `W ⊆ Q 0` or `W ⊆ Q 4`. So `W ⊆ ⋃Δ(𝒫)` by (3).
2. Take `v ∈ W`, the member `Y ∈ Δ(𝒫)` through `v`, and the strand `T` of `Y`.
3. `S ⊄ Y`. Otherwise take `z ∈ K ∩ Q 2` (`Cl K` meets the open `Q 2`, so `K` does). §2 makes `Y` a
   layer of `S`, but a layer cannot contain the whole strand.
4. If `S ⊄ T`, Lemma 7 applies (`T∖S ≠ ∅` through `P 2`). If `S ⊆ T`, `layers_agree` applies, and
   its first alternative would put `S` inside `Y`.
5. Either way `Y` is a layer of `S` through `v`, so `Y = W`.

This is Hagopian's "(3) and Lemma 7", with §2 for the case `S ⊆ Y`.

**4.3 (6)** (skeleton: `CoverData84.invariant`). The chains are `R ∈ {𝒫} ∪ {𝒫(Z): Z ∈ S}`, finitely
many. Let `δ` be the least, over these chains, of two numbers: the `ε` of Lemma 15 for `R`
(`hagopian84_lemma15`), and the `η` of `delta5_dist_pos` for `R`.

Let `D ∈ Δ(R)` and let `h` be a `δ`-homeomorphism.
1. `h[D] ∈ Ω(R)` (Lemma 15).
2. `h[D] ⊆ midUnion R`: each point of `D ⊆ ⋃Δ(R)` moves less than `η`.
3. 4.1 or 4.2 then gives `h[D] ∈ 𝔇`.

Hagopian's proof of Lemma 15 takes `ε = ½ρ(⋃Δ(𝒫), M∖⋃𝒫′)`, which already keeps `h[Z]` inside
`⋃𝒫′`. Only the statement of Lemma 15 (and `hagopian84_lemma15`) drops that bound, so the `η` here
makes explicit what his proof supplies.

## 5. The package (skeleton: `CoverData84.isJonesDecomp`, `hagopian84_decomp`)

1. **`usc`.**
   * *Closed:* members are layers, so they are closed.
   * *U.s.c.:* for an open `U`, show that `{z : cls z ⊆ U}` is open. Take `z₀` in it, and let
     `D = cls z₀ ∈ Δ(R)`. Pick `ε` with `thickening ε D ⊆ U`.
   * Lemma 14 for `R` at `z₀` gives `δ`. Also `⋃Δ(R)` is open (`isOpen_sUnion_delta5`).
   * A point `z′` close to `z₀` lies in some `D′ ∈ Δ(R)`, and `D′ = cls z′` by 3.4. Lemma 14 gives
     `D′ ⊆ thickening ε D ⊆ U`.
   * Hagopian: "It follows from Lemma 14 that `𝔇` is continuous". Only the u.s.c. half is needed.
2. **`conn`:** layers are connected and nonempty (`layer_isPreconnected'`, `layer_nonempty'`).
3. **`proper`:** a member of `Δ(R)` misses `Cl(R 0 ∪ R 4)`, and `R 0 ≠ ∅`.
4. **`invariant`:** this is (6).
5. **`arc`:**
   * `midUnion P` is nonempty (`P 1 ∩ P 2 ≠ ∅`). Take a strand `G` of `𝒫` and its map `c` running
     straight (regularity).
   * `exists_interval_in_delta` gives `[a, b]` with every layer in `Δ(𝒫)`.
   * Let `C = c⁻¹[[a, b]]` with the map of `minimalAdmissible_restrict`. Its fibres are members of
     `𝔇`, so by 3.4 they are exactly the traces of the classes.
6. **`hagopian84_decomp`**: `hagopian84Decomp_of_package`, with the setoid of
   `exists_coverData84`.
7. **`hagopian76_theorem1_jones (hA : NoArcIndecHomPlane) : Hagopian76Thm1`**, which is
   `hagopian76_theorem1_of_jones hagopian84_decomp hA`. In `Hagopian84A.lean` replace the
   commented-out blocks by pointers.
8. **The printed closedness of `⋃𝔅`** (skeleton: `sUnion_cover84_eq_univ`). For any choice as in
   `exists_finite_cover84`, `⋃Δ(𝒫) ∪ ⋃_{Z ∈ Ω(𝒫)∖Δ(𝒫)} ⋃Δ(𝒫(Z)) = M`. This is a corollary of
   `exists_finite_cover84`. Update the §5 comment of `Hagopian84C.lean`, `OPEN.md`, and H84.29.

## 6. Order

§2, §3, §4, §5. §5.8 is independent and short.

## 7. Places to check (candidate ledger entries)

1. **p. 344, disjointness, first case:** the hypothesis `E∖F ≠ ∅` of Lemma 7 for the strands, and
   the case `S_A ⊆ Y` (3.4).
2. **(5):** the printed "(3) and Lemma 7" needs §2 at the case `S ⊆ Y` (4.2). **(6):** the bound
   `η` is in the proof of Lemma 15 but not in its statement (4.3).
3. **"It follows from Lemma 14 that `𝔇` is continuous":** say whether the lower semicontinuous half
   also follows; it is not needed.
4. **p. 344, "first note that for each integer `i` …, each component of `⋃Δ𝒫(Zᵢ)` misses `P₃`
   and intersects `M∖⋃𝒫′`":** it is not used on this route. It would close the first case of
   disjointness (3.4) but is itself unargued. Say whether it needs the end-set positions of
   `J(Z)`, or more.
5. **H84.29:** reclassify per §0 (the statement is true; the printed reason is not an argument).

## 8. Deliverables

1. **The items of §2–§5.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch188.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
     `CoverData84` is one.
2. **`LEDGER.md`:** a subsection "Hagopian 1984 V (batch 188)" in the Hagopian 1984 section, with
   the printed sentences quoted.
3. **Notes:** `doc/notes/hagopian84.md` (the transfer lemma, disjointness, (5), (6), the package).
4. **Publish the changes, as in batch 187.** At the end of the run:
   * create `doc/batches/batch188-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch188-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of `Hagopian76Thm1` on the 1984 route;
   * a skeleton proposal for the arc step, `NoArcIndecHomPlane`, from Jones 1975
     (`doc/sources/jones1975.pdf`, `doc/notes/jones75.md`). List Jones's steps, the repository
     material each uses, and the named claims a first batch would need.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
