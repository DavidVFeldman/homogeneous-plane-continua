# Commission: batch 184 — Part E, Hagopian 1976 XXIX: Theorem 1 by Jones's plan (Hagopian 1984)

**Go!** This batch runs on top of the batch-183 work. Three files come with it, as separate uploads:

* `COMMISSION-batch184.md`: this text, also pasted into the prompt.
* `Hagopian84A.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian84A.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian84A` at the end of `HPC.lean`.
* `hagopian1984.pdf`: C. L. Hagopian, *Atriodic homogeneous continua*, Pacific J. Math. 113 (1984),
  333–347.
  * Save it as `doc/sources/hagopian1984.pdf`.
  * Journal pp. 333–347 are PDF pages 2–16 (journal page = PDF page + 331).
  * Read it from page images rendered at 200 dpi or more, not from extracted text.

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
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1984 I (batch 184)");
  * `README.md`;
  * `LEDGER.md`: a new section for Hagopian 1984, after the Hagopian 1976 section;
  * `OPEN.md`.
* New files: `doc/notes/hagopian84.md`, the new Lean files, the batch files of §9.
* The 1976-route files stay as they are: `Hagopian76*.lean`, `H76*.lean`,
  `doc/notes/hagopian76-cases.md`. Batch 185 returns to them.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 183

* **Delivery.** The tarball and the manifest worked again. Keep doing it (§9.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2180 lines (2160 + 20 added, none removed), with `sorryAx` in none.
  The 20 new declarations use only the standard three axioms.

**Accepted, all of it**, including the non-vacuity notes.
* **`E24Claims`.** My check agrees with your §7. With `B = Cl Cᵢ ⊆ L`, under Property 2 it amounts
  to `ρ(yᵢ₋₁, Cl Cᵢ) ≥ ε₃`. That is stronger than the conclusion, and the work sits in the three
  sub-claims.
* **Thank you** for two corrections.
  * The parity point: Bing's Case 2 sentence holds whichever way the gap arc runs.
  * The test of my orientation proposal, which fails as stated. My ledger records it as my error.

**Change of plan.** Hagopian re-proved Theorem 1 in 1984 by F. B. Jones's plan, without the case
analysis of pp. 348–349 (§1). From now on, batches alternate:
* this batch starts the 1984 route;
* batch 185 returns to pp. 348–349, with saturation and "between" first.

## 1. The source and the plan

Hagopian 1984, p. 346 (my transcription from the page images at 200 dpi; check it):

> In 1968 F. B. Jones [16] suggested the following method for proving that every indecomposable
> homogeneous plane continuum `M` is hereditarily indecomposable. Assume that `M` has a decomposable
> subcontinuum. Find a monotone decomposition `𝔇` of `M` such that `M/𝔇` is a homogeneous plane
> continuum that contains an arc. It follows from a theorem of Bing [4] that `M/𝔇` is a simple
> closed curve and this contradicts the fact that `M` is indecomposable.
>
> Every indecomposable homogeneous plane continuum is atriodic [10, Lemma 1]. In Theorem 2 (above),
> since the elements of `𝔇` are tree-like, if `M` is planar, then `M/𝔇` is planar [21]. Hence
> Theorem 2 provides the decomposition that Jones requested and we obtain the following:
>
> COROLLARY 3. *Every indecomposable homogeneous plane continuum is hereditarily indecomposable*
> [11].

Here [4] is Bing 1960, [10] Hagopian 1975, [11] Hagopian 1976, [16] Jones's 1969 Auburn paper, and
[21] Moore 1925.

**The route for this project.** Let `M` be an indecomposable homogeneous plane continuum with a
decomposable subcontinuum.
1. `M` is atriodic and hereditarily unicoherent (`hagopian75_lemma1`, verified). This gives the
   standing hypothesis of the paper's §3. It also gives Lemma 2, which the paper cites to
   Mackowiak–Tymchatyn [20, Theorem 13.8], without [20].
2. Apply Theorem 1 of the paper with `N = M`.
   * "`M = N`" is then given. So Lemma 10 and claim (4) of the proof (the density of `S`) are not
     needed.
   * Needed: the decomposition `𝔇`, its continuity, the homogeneity of `M/𝔇`, and an arc in `M/𝔇`.
3. **Planarity.** Extend `𝔇` by the points of the plane off `M`.
   * The elements are points or proper subcontinua of `M`. So they do not separate the plane
     (`no_proper_subcontinuum_separates`).
   * Upper semicontinuity comes from the continuity of `𝔇`.
   * Then Moore 1925 Theorem 22 applies (`m25_theorem22`; compare `layerSetoid_mooreDecomp` and
     `exists_quotient_plane`). So `M/𝔇` is a plane continuum.
   * Hagopian uses the tree-likeness of the elements instead, through Rogers [25]. That is not
     needed here.
4. `M/𝔇` is indecomposable (a monotone image of `M`), homogeneous, and contains an arc.
5. **The arc step:** no indecomposable homogeneous plane continuum contains an arc. This is Bing [4]
   in the indecomposable case; F. B. Jones, Houston J. Math. 1 (1975), 57–61, gives another proof.
   This batch keeps it as the named `Prop` `NoArcIndecHomPlane`. Its source will be decided later.

Corollary 3 goes through Theorem 2, which assumes that `M` is not a solenoid. Theorem 1 with
`N = M` needs no such hypothesis. If `𝔇` has only points, then `M/𝔇 = M`.

The route uses Hagopian 1976 only through its Lemmas 3–6 (the 1984 Lemmas 3, 4, 5, 11). It uses
nothing from pp. 345–349.

## 2. Transcription and dictionary (`doc/notes/hagopian84.md`)

1. **Transcribe from the page images:**
   * the §2 definitions (type λ, the decomposition);
   * the §3 definitions and notation: ε-homeomorphism, `W(x, ε)`, end sets, extension away,
     `𝔖(k⁻¹(0), E)`, essential subcontinuum, 5-linked chain, `𝔏′`, free, normal, runs straight
     ((1)–(5)), regular, ordered refinement, `Ω(𝒫)`, `Δ(𝒫)`;
   * Lemmas 1–16 with their proofs, and Theorem 1 with its proof;
   * the Corollary 3 paragraph.
2. **Dictionary with the repository.** My mapping, to check and correct:

| Hagopian 1984 | repository |
| --- | --- |
| type λ ("There they are called continua of type `A′`", p. 335) | `IsTypeA'`, `IsMinimalAdmissible` |
| "the decomposition of `M`" (p. 335) | the minimal admissible map; uniqueness: `hagopian75_lemma3_unique` |
| extension away from `k⁻¹(0)`; `𝔖(k⁻¹(0), E)` | `IsExtensionAway`; `extUnion` |
| "essential subcontinuum of `E`" (p. 336: meets more than one element of the decomposition of `E`) | *not* `IsEssential`, which means essential to `R(E)`; a new definition |
| `W(x, ε)`; Lemma 1 | `Wset`; `hagopian75_lemma4`, `effros_homogeneous` |
| Lemma 2 | `hagopian75_lemma1_hu` |
| Lemma 3 | `hagopian76_lemma3` (check that the hypotheses agree) |
| Lemmas 4, 5 | `hagopian76_lemma4`, `hagopian76_lemma5` |
| Lemma 6 ("[26, Theorem 8, page 14]") | the end-set property (my ledger, A.23, p. 340); find or prove |
| Lemma 9 | `hagopian75_layer_homogeneous` |
| Lemma 11 ("paragraphs 2 through 11 in the proof of Lemma 6 of [11]") | `hagopian76_lemma6` (one of its versions) |
| chains, ordered refinement | the 1976 chain definitions (`IsPlaneChain`, `IsOrderedRefinement`), if they fit |
| Moore 1962 [22, Theorem 44, page 15] (Lemma 12) | find or prove |
| "paragraphs 1 and 2 in the proof of Theorem 1 of [10]" (Theorem 1, p. 342) | `hagopian75_exists_typeA'` |

## 3. The assembly

The skeleton states:
* `NoArcIndecHomPlane`: no indecomposable homogeneous plane continuum contains an arc;
* `Hagopian84Decomp`: the decomposition of Jones's plan, for a plane `M` (Theorem 1 with `N = M`).
  The shape may be adjusted; record the changes;
* `hagopian76_theorem1_of_jones`: from the two, `Hagopian76Thm1`.

**Prove `hagopian76_theorem1_of_jones`** (steps 3–5 of §1). Expected pieces:
1. **The plane quotient.** Let `q : M → Y` be continuous and surjective, with connected fibres, each
   fibre `≠ M`. Then some compact `Q` in the plane is homeomorphic to `Y`. Use Moore 1925, through
   the decomposition of the plane into the fibres and the points off `M`.
2. **Monotone images.** A monotone image of an indecomposable continuum is indecomposable. For a
   closed monotone map, the preimages of subcontinua are subcontinua.
3. **The contradiction**, with `NoArcIndecHomPlane` applied to `Q`.

**Also prove `hagopian75_theorem1_of_noArc`.** This is Hagopian 1975 Theorem 1, with paragraph 4
supplied by `NoArcIndecHomPlane` and `exists_arc_of_degenerate_layers`. Paragraph 4 was set aside in
batch 155 (`hagopian75_theorem1_of_layer`).

**Non-vacuity notes for both named `Prop`s.** My reading, to check:
* Both are used inside a proof by contradiction, about an `M` that Theorem 1 says does not exist
  (the standing remark of the 1976 work).
* `NoArcIndecHomPlane` is a published theorem (Bing 1960), independent of Hagopian 1976.
* `Hagopian84Decomp` alone does not give Theorem 1, which needs `NoArcIndecHomPlane` as well.
* Check that the shape of `Hagopian84Decomp` asks for nothing that is false in a short argument
  (for instance, that every fibre be nondegenerate).

## 4. Lemmas 6–8 and 12–16 (and Lemma 10, if cheap)

**The setting is your choice; say which you take.**
* Plane `M`: compact, connected, homogeneous and indecomposable. Atriodicity and hereditary
  unicoherence come from §1 step 1.
* Or a compact metric atriodic homogeneous continuum, with Lemma 2 as a hypothesis. Effros is in
  `HPC.Effros`.

**For each lemma:** the statement and the proof, with each unargued step either supplied or
recorded. These are the unargued steps I noticed. They are candidate ledger entries; check each.

1. **Lemma 7.**
   * "Since `M` is atriodic, it follows from (1) that there is a point `x` of `F` in `H∖k⁻¹(r)`."
   * "this contradicts the fact that `J` is irreducible between `x` and `k⁻¹(r)`": irreducibility
     between a point of one end set and the other end set.
   * "Suppose that (2) is false. Then `F ∩ J` does not contain `k⁻¹(r)`."
2. **Lemma 2 applied to unions.** Lemma 2 is applied to unions of two subcontinua (`F ∪ J` in
   Lemma 7, `N ∪ F` in Lemma 10, and others), which must be proper. That is automatic when `M` is
   indecomposable. Record where it is unargued for a general atriodic `M`.
3. **Lemma 8.**
   * "The quotient space `(E ∪ F)/𝔇` is the union of two arcs."
   * "Since `M` is atriodic, `(E ∪ F)/𝔇` is atriodic": the monotone preimage of a triod is a triod.
   * "It follows from Lemma 2 that `(E ∪ F)/𝔇` does not contain a simple closed curve", and hence
     that it is an arc.
4. **Lemma 12.**
   * "Since `𝔏` is regular, `E∖(A ∪ B)` is an essential subcontinuum of `E`."
   * "Since `M` is atriodic, `E∖(A ∪ B)` is a component of `M∖(A ∪ B)`."
   * "The chain `𝒫` … is a free normal regular ordered refinement of `𝔏`. Note that `E` runs
     straight through `𝒫`."
5. **Lemma 13.**
   * "Note that `𝔏` is a normal chain in `M∖A`."
   * In (3): "It follows from the definition of `δ` that `r ∈ [x₂, x₁₃]∖[x₃ᵢ₋₃, x₃ᵢ]`"; the
     choice of `s` and `g`; and the hypotheses of Lemma 3 in "By Lemma 3,
     `g[k⁻¹(s)] = h[k⁻¹(r)]`".
   * In (4): the `μ`-homeomorphism `f` with `fh` a `δ`-homeomorphism and `f(p) ∈ Lᵢ`.
   * In (5): "Since `M` is atriodic and `g[k⁻¹[0, x₃ᵢ]]` misses `Lᵢ₊₁∖Lᵢ`, it follows that …".
   * Regularity: "Since `M` is atriodic, it follows from (6) and Lemma 6 that `Cl K` is an essential
     subcontinuum of `h[E]`."
   * The last paragraph: why each component `K` of `⋃𝒫′` meets some `h[E]` with `h` a
     `δ`-homeomorphism.
6. **Lemma 14.**
   * "By Lemma 3, if `zᵢ` belongs to the open set `W(z, ε)` …, then there is an ε-homeomorphism `h`
     … such that `h[Z] = Zᵢ`": which hypotheses of Lemma 3 are used, and why they hold.
   * "Since `ε` is arbitrarily small, `{Zᵢ}` converges to `Z`": in which sense, and that this gives
     continuity (upper and lower semicontinuity).
7. **Lemma 15:** the same use of Lemma 3.
8. **Lemma 16.**
   * "Since `𝔇` is continuous (Lemma 5), `s ∉ S` and `s ≠ 1`."
   * "Since `𝒫` is free, there exist a 3-linked subchain `𝔔` of `𝒫` and numbers `t`, `w` greater
     than `s` such that (1) …"
   * The final appeal to the uniqueness of the decomposition.

## 5. Theorem 1 with `N = M`

Target: `Hagopian84Decomp`, or the strongest conditional form. The steps of pp. 342–345:
1. **The chain.** `E ⊆ M` of type λ (`hagopian75_exists_typeA'`), and `𝒫` from Lemma 13 with (1).
2. **For `Z ∈ Ω(𝒫)∖Δ(𝒫)`:** `K(Z)`, `X(Z)`, `F(Z)`, `J(Z)`, and `𝒫(Z)` with (2), (3). Unargued
   steps:
   * "the end set of `Cl K(Z)` that is separated from `Z` in `Cl K(Z)` by `P₃`".
   * "By Lemma 11, `Cl ⋃𝔖(X(Z), Cl K(Z))` is an indecomposable subcontinuum of `N`." Lemma 11
     needs `Cl K(Z) ⊆ N`, while `Cl K(Z)` is essential in `h[E] ⊆ h[N]`. This is automatic for
     `N = M`. Record whether the general case needs `h[N]` in place of `N`.
   * "Thus `⋃𝔖(X(Z), Cl K(Z))` intersects `P₃∖K(Z)`." My reading, to check: otherwise
     `Cl ⋃𝔖 ∩ P₃` would be a nonempty open subset of `Cl ⋃𝔖` inside its proper subcontinuum
     `Cl K(Z)`. An indecomposable continuum has no such subset.
   * "Hence there is an essential subcontinuum `J(Z)` of `F(Z)` that contains `Z`, misses `Cl P₃`,
     …".
3. **The cover:** "it follows that `⋃𝔅` is a closed open subset of `M`. Hence `𝔅` covers `M`."
4. **The decomposition:** the finite subcover, `𝔇`, and disjointness ("by (2), (3), and Lemma 7,
   `A = B`"; "Thus, by Lemma 3, `A = B`").
5. **Its elements:** continuity (Lemma 14). The elements are points or homogeneous continua
   (Lemma 9); also check that they are proper subcontinua, being layers of type λ continua.
6. **Homogeneity:** (5), (6), and the homogeneity of `M/𝔇` through the chain of the sets
   `W(xᵢ, δ/2)`.
7. **An arc in `M/𝔇`.** The paper does not argue it (p. 344: "Since `M/𝔇` is an atriodic
   homogeneous continuum that contains an arc"). Supply it. For example, take `K` a component of
   `⋃𝒫′` and an essential subcontinuum of `Cl K`. Its layers that miss `Cl(P₁ ∪ P₅)` are elements
   of `Δ(𝒫) ⊆ 𝔇`, and their union maps onto an arc.

Not needed here:
* claim (4) (`S` dense) and Lemma 10;
* "`M/𝔇` is a solenoid" ([20, Theorem 14.4]);
* the tree-likeness of the elements ([25]).

## 6. Last, if time remains: the arc step, reconnaissance only

`NoArcIndecHomPlane` will come from Bing 1960 (`doc/sources/bing1960.pdf`) or from Jones 1975 (not
in the repository). List what Bing's proof of the indecomposable case uses (§§2–10: his Properties
and Theorems), and which of it the repository already has. Do not formalize any of it.

## 7. Order

1. §2 (transcription, dictionary).
2. §3 (the assembly).
3. §4.
4. §5.
5. §6.

## 8. Places to check (candidate ledger entries)

1. **p. 335:** "If a continuum `M` is of type λ, then `M` admits a unique monotone upper
   semi-continuous decomposition … [19, Theorem 3, page 216] [26, Theorem 10, page 15]". Compare the
   citation in Hagopian 1975's Lemma 2. There, Kuratowski's Theorem 3 gives the order type, not
   type A′.
2. **The unargued steps** of §4 and §5.
3. **p. 344:** "`M/𝔇` … contains an arc", unargued.
4. **p. 346:** "since the elements of `𝔇` are tree-like, if `M` is planar, then `M/𝔇` is planar
   [21]".
   * Moore 1925 needs elements that do not separate the plane.
   * That a tree-like continuum does not separate the plane is not stated.
   * Our route uses `no_proper_subcontinuum_separates` instead.
5. **Corollary 3** goes through Theorem 2 ("not a solenoid") rather than Theorem 1 with `N = M`.
6. **Small slips.**
   * "opens sets" (p. 333), "ε-circluar" (p. 334), "ε-homomorphisms" (p. 338).
   * "In 1968 F. B. Jones [16]" (p. 346), against "(1969)" in the reference list (p. 347) and the
     1976 abstract ("At the Auburn Topology Conference in 1969").

## 9. Deliverables

1. **The items of §2–§6.**
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch184.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
2. **`LEDGER.md`:** the new Hagopian 1984 section, with the outcome of each check and the printed
   sentences quoted.
3. **`doc/notes/hagopian84.md`:** the transcription, the dictionary, and the route of §1.
4. **Publish the changes, as in batch 183.** At the end of the run:
   * create `doc/batches/batch184-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch184-MANIFEST.txt`;
   * publish both, as you published the report.
5. **The report.** Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, for both routes (the 1976 map of report 183, unchanged, and
     the new one);
   * a skeleton proposal for what remains.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/`, `doc/batches/skeletons/` and `doc/sources/`.
   * Nothing is left at the root.
