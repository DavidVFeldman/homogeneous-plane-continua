# Commission: batch 183 — Part E, Hagopian 1976 XXVIII: Theorem 1 — Bing's reasons for Cases 1–2; E2.4; the orientation; saturation

**Go!** This batch runs on top of the batch-182 work. Two files come with it, as separate uploads:

* `COMMISSION-batch183.md`: this text, also pasted into the prompt.
* `Hagopian76AB.lean`: the skeleton.
  * Save it as `HPC/Hagopian/Hagopian76AB.lean`. You may split it under `HPC/Hagopian/`.
  * Add `import HPC.Hagopian.Hagopian76AB` at the end of `HPC.lean`.

**Source.** No new file. Bing 1960 is already in the repository (`doc/sources/bing1960.pdf`).
Journal pp. 224–228 are PDF pages 16–20. Read them from page images rendered at 200 dpi or more,
not from extracted text.

**Rules.**
* Shapes may be adjusted. Record each change at the statement and in the report.
* The first line of the report names the commission it read.
* Report each item as *proved*, *refuted*, or *open with the obstruction stated*.
* If you leave out something this commission asks for, list it in the report's §0 with the reason.
* **Non-vacuity (standing rule).** For every theorem whose hypotheses include a named `Prop` or a
  structure standing for open work, the report gives a note with the two checks of commission 182.
* Edit no existing file except:
  * `HPC.lean`;
  * `Axioms.lean` and `axioms.txt` (new group "Hagopian 1976 XXVIII (batch 183)");
  * `README.md`;
  * `LEDGER.md` §6;
  * `OPEN.md`;
  * the earlier `HPC/Hagopian/Hagopian76*.lean` files: delete the commented-out copies of statements
    proved here, leaving one-line pointers;
  * `doc/notes/hagopian76-cases.md`: add the correspondence with Bing (§1) and the routes below.

**Progress lines** as before: `STATUS: <item> proved / open (<obstruction>)`, and
`STATUS: need help (<what>)` when stuck.

## 0. On batch 182

* **Delivery.** The tarball and the manifest worked again. Keep doing it (§9.4).
* **Copies.** The skeleton and commission copies are byte-identical.
* **Audit.** `axioms.txt` has 2160 lines (2115 + 45 added, none removed), with `sorryAx` in none.
  The 45 new declarations use only the standard three axioms.

**Accepted, all of it**, including the non-vacuity notes.

**Thank you for the padded block sequences.** `IsBlocks` was Aristotle's structure from batch 179,
and I accepted it in three audits. Moving the reduction to tight sequences is right (ledger C.3).

**On E2.4 (your §4.2).** You took `H = N`, the subcontinuum of `L` between `yᵢ` and `yᵢ₋₁`, and
showed correctly that its end sets need not be close. The text says only "a subcontinuum of `L`",
and my commission did not name one. Bing names it (§2 below), and it is not `N`.

## 1. Bing 1960 is the model for pp. 348–349

Hagopian writes "Following Bing [2, p. 225]" (p. 348). Cases 1–2 follow Bing pp. 225–227 nearly line
for line, and Bing gives several reasons that Hagopian leaves out. The dictionary below is my
reading; check it against the pages.

| Hagopian 1976 | Bing 1960 |
| --- | --- |
| `K`, the low vertical over `p₃`; `yᵢ ∈ K` | `K`, the disc bounded by `a₁a₅`, `a₁r`, `rs`, `a₅s`; `p ∈ K·(M′ − A)` above `a₃` |
| `d⁻¹[I]`, `d⁻¹[J]`; `I` above `J` | arcs `x₂ᵢ₋₁x₂ᵢ`, `x₂ᵢ₊₁x₂ᵢ₊₂` (Bing's indices increase downward) |
| the gap continuum `d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]` | the gap arc `x₂ᵢx₂ᵢ₊₁` |
| `f = h₁h⁻¹`, an `ε₃`-homeomorphism | `h`, an `ε₄`-homeomorphism |
| Property 2 (`ε₂`, `ε₃`) | Property 18 (`ε₃`, `ε₄`): an arc `ab` with `ρ(a, b) < ε₄` has diameter `< ε₃` or is `ε₃`-dense |
| `Cᵢ`, `Cᵢ₋₁`, `L`, `N` | `tu`, `vw`, the arc `tuvw` |
| `π⁻¹(p₄)` (Case 1) | `a₄` (Case 1); `a₂` in Case 2 |
| `L ∩ F = ∅` (composants) | `tuvw ⊆ M′ − A` (arc components) |
| the band `P = d⁻¹[[x₂ᵢ₋₃, x₂ᵢ]] ∪ Q` | the simple closed curve `J` |

The sentences that matter (pp. 226–227, my transcription from the page images):
[Quotation moved to doc/sources/transcriptions/bing1960.md, §doc/batches/COMMISSION-batch183.md, The sentences that matter (pp. 226–227); batch 204.]

Add the dictionary and these routes to `doc/notes/hagopian76-cases.md`. Record in `LEDGER.md` which
of Bing's reasons carry over to continua, and which need a new argument.

## 2. E2.4 by Bing's arc `ab`

The subcontinuum `H ⊆ L` has its ends close together across one strand:
1. **If `Cᵢ₋₁` lies between `Cᵢ` and `S_I`** (Bing: "`q` above `tu`"). Put `a = yᵢ`.
   * `yᵢ` lies below `S_I` and `f(yᵢ)` above it, so `ρ(yᵢ, Cl S_I) < ε₃` (`cross_strand_near`).
   * The short segment from `yᵢ` to a nearest point of `Cl S_I` crosses `Cl Cᵢ₋₁`. Apply the cap
     lemma with `W = Cᵢ₋₁`; it is a crossing piece by §6.
   * That gives `b ∈ Cl Cᵢ₋₁` with `ρ(a, b) < ε₃`.
2. **If `Cᵢ₋₁` lies below `Cᵢ` and `ρ(yᵢ₋₁, Cl S_I) < ε₃`** (Bing's second case). Here `S_I` is the
   `I`-strand adjacent above `yᵢ` (and, by §3, above `yᵢ₋₁`); the witness field `far` already uses
   `Cl S_I`. Put `b = yᵢ₋₁`.
   * Take `w` on `S_I` with `ρ(yᵢ₋₁, w) < ε₃`.
   * `S_I` lies above `Cᵢ`, and `Cᵢ₋₁` below it. So the segment from `yᵢ₋₁` to `w` crosses `Cl Cᵢ`
     (cap lemma with `W = Cᵢ`), at a point `a` with `ρ(a, b) < ε₃`.
   * Bing's single `I`-arc becomes several `I`-strands here, which may interleave with the
     `J`-strands. For that reason the claim is stated for the adjacent strand `S_I`, not for all of
     `d⁻¹[I]` as printed. Say in the report whether the printed form (`d⁻¹[I]`) holds, or fails
     for an `I`-strand below `Cᵢ`.
3. **`H`**: the subcontinuum of `L` between the layer of `L` through `a` and the layer through `b`,
   with the decomposition of `L` restricted and reparametrized. You proposed
   `minimalAdmissible_restrict`. Its end sets `T ∋ a`, `V ∋ b` satisfy `ρ(T, V) < ε₃`.
4. **A far layer.** `H` runs out to the side segment and around (Case 1: the left side). Some layer
   `U` of `H` has `ρ(T, U) > ε₂`. If this needs `ε₂` below a constant fixed by `D` (for instance the
   distance from `Mid` to the side preimages), add the bound to the set-up and say why.
5. **Essential to `h[R(E)]`.** `H` contains a piece of `Cl Cᵢ` and lies in `L`.
6. **The contradiction.** Property 2 makes every point of `R(E)` lie within `ε₂` of `H`. But `H`
   does not come within `ε₂` of `π⁻¹(p₄)` in Case 1, or of `π⁻¹(p₂)` in Case 2 (Bing uses `a₂`
   there).
   * This is the open T17 sentence: "Since `L − {L₁, L₁₁}` follows `Cl Cᵢ₋₁` and `Cl Cᵢ`, the
     continuum `N` does not come within `ε₂` of `π⁻¹(p₄)`."
   * Prove it for `H` from the chain `L` (Property 1, `hP1`) and the strand positions (S6).
   * Or state it as a named `Prop`, with the configuration that blocks it. One risk: `L`, outside
     `D`, entering a pocket from the far side near `p₄`.

Prove `property2_violation` (skeleton) in this form, or the strongest conditional form.

## 3. "Between" (Case 1, commission 181 §3.4) by Bing's Jordan-curve argument

Bing: the arc leaves `K` at `u` between `x₂ᵢ` and `x₂ᵢ₊₁` on one side line. It cannot meet the gap
arc, which lies in another arc component. So it re-enters `K` between the same two points.

The continuum form:
* `L` leaves `Cl Cᵢ` through the left side segment (Case 1). Its exit point lies between the points
  where `Cl S_J` and `Cl S_I` meet that segment, because `Cᵢ` is between the two strands.
* The gap continuum `Γ = d⁻¹[[x₂ᵢ₋₂, x₂ᵢ₋₁]]` joins `d⁻¹[J]` to `d⁻¹[I]`.
* `Cl S_J ∪ Γ ∪ Cl S_I` together with the part of the side segment between the strands' ends cuts
  off a region (`separatesPlane_union_of_inter_disconnected`, `sepIn_iff_separatesPts_union`).
* `L ∩ F = ∅` (`extension_misses_G`), so `L` stays in that region until it re-enters `D` through the
  same part of the side segment.
* Hence `Cᵢ₋₁`, the first crossing component met, lies between `S_J` and `S_I`.

Your batch-180 configuration ("`L` leaves `D` through a side segment and re-enters on the other side
of a strand's end") is excluded if `Γ` closes that region. Decide whether it does. This is where the
case hypothesis "`d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)` meet the same side" enters. If the region is closed
by `Γ` only partly, describe how.

## 4. Case 2 by Bing's closed curve

1. **(a)** "If `v` is above `x₂ᵢ₊₁x₂ᵢ₊₂` it is between the points `x₂ᵢ` and `x₂ᵢ₊₂`": the argument
   of §3, at the right side segment.
2. **(b) and (e)**: the closed curve. In Hagopian's terms take
   `P = Q ∪ (the part of d⁻¹[I] right of Q) ∪ Γ ∪ (the part of d⁻¹[J] left of Q)`, with `Q` on the
   vertical over `15/22`. The image `f[N]` misses `P`:
   * it misses `F` by composants;
   * it misses `Q` if `N` is `ε₂`-far from `Q` and `ε₃ < ε₂`. That is commission 181 §3.6.4, and
     Bing's "no point of the arc `pq` in `M` is within `ε₄` of this vertical part of `J`", which
     Bing does not argue either.

   So `f(yᵢ₋₁)` lies in the same complementary domain of `P` as `f(yᵢ)`, which is above `S_I`. On my
   reading, if `Γ` passes outside `D` on the `I₂` side (Bing's Figure 3), that domain misses
   everything below `S_J`. That gives (e) and, after the good case is split off, (b).
3. **The open point.** Can `Γ` pass outside `D` on the `E` side instead, around an end of `π[E]`? If
   it cannot, prove it. If it can, give the configuration: it is then a gap in Bing as well as in
   Hagopian.
4. **(d)** as §2, with `π⁻¹(p₂)` in place of `π⁻¹(p₄)`.

## 5. The two other orientations

Batch 182 treats `d⁻¹[J]` on the side of `yᵢ` and its mirror. When `d⁻¹[J]` is on the side of
`f(yᵢ)`, E1 leaves `f(yᵢ)` between the strands. `f(yᵢ)` is not on Hagopian's `K`, which is an arc,
whereas Bing's `K` is a disc. Proposal, to test:
* state Property 4 for points of `Mid ∩ π⁻¹[D]` (abscissae in `[1/2 − 2/n, 1/2 + 2/n]`), not only
  points of `K`;
* carry it for `f` or for `f⁻¹`. For `f⁻¹ = h h₁⁻¹`, the roles of `h` and `h₁` swap, and the
  composant data (`hcomp`) are symmetric;
* in the bad orientation, run the step from `f(yᵢ)` with `f⁻¹`.

Check that the endgame survives:
* the top block uses `p`;
* the base `[x₁, x₂]` separates nothing in `π⁻¹[D]`;
* E2.1 needs a point of `Cᵢ₋₁` over `1/2`, and `K` supplies it.

If the proposal fails, say where.

## 6. Smaller items

1. **E2.1 items 1–3, 5** (commission 182 §4.1): the first crossing component met by an extension of
   `Cl Cᵢ` away from `X`, the shortest `L`, and `Cᵢ₋₁` a crossing piece with `Cl Cᵢ₋₁` essential.
2. **Saturation**:
   * steps 4–5 of `noncrossing_half_in_O`: S0 sends the two halves of the translate in opposite
     horizontal directions;
   * the points `zⱼ` and (iii) at `zⱼ`;
   * the two edge cases.
3. **The case split for `i ≥ 3`.** Bing's `x₂ᵢ`, `x₂ᵢ₊₁` lie on the side lines by construction,
   being ends of arcs irreducible between them. Consider replacing Hagopian's split, which is about
   the layers `d⁻¹(x₂ᵢ₋₁)` and `d⁻¹(x₂ᵢ₋₂)`, by what §3 and §4 actually use: on which side `Γ` joins
   the left ends or the right ends of `S_J` and `S_I`. State that split and decide whether it is
   exhaustive.

## 7. Order

1. §2 (E2.4) and §3 ("between").
2. §4 (Case 2).
3. §5 (orientation).
4. §6.

## 8. Places to check (candidate ledger entries)

1. **pp. 348–349 against Bing 1960 pp. 225–227**: which of Bing's reasons carry over, sentence by
   sentence.
2. **p. 348, E2.4**: the subcontinuum is Bing's `ab`, not `N`.
3. **p. 348, "`N` does not come within `ε₂` of `π⁻¹(p₄)`"**: and Bing's "no point of the arc `pq`
   in `M` is within `ε₄` of this vertical part of `J` above `a₄`", which is also unargued.
4. **p. 349, Case 2**: (a), (b), (e) through §4; `p₂` versus `p₄`.
5. **p. 348, "(Other cases …)"**: Bing's disc against Hagopian's arc `K` (§5).

## 9. Deliverables

1. The items of §2–§6.
   * `#print axioms` for every new theorem goes to `doc/batches/audits/axioms-batch183.txt`.
   * Regenerate `axioms.txt`. `sorryAx` should appear in no line.
   * Anything left open is commented out, with the obstruction stated in `OPEN.md`.
   * Named `Prop`s and structures are listed in the report, each with its non-vacuity note.
2. `LEDGER.md` §6: a subsection for this batch, with the outcome of each check and the printed
   sentences quoted, Hagopian's and Bing's.
3. `doc/notes/hagopian76-cases.md`: the dictionary of §1 and the routes of §2–§5.
4. **Publish the changes, as in batch 182.** At the end of the run:
   * create `doc/batches/batch183-files.tar.gz` with every file added or changed in this run;
   * take the list from `git diff --name-status` against the run's initial commit, plus any
     uncommitted change;
   * write the list in `doc/batches/batch183-MANIFEST.txt`;
   * publish both, as you published the report.
5. The report. Its first line names the commission it read. It covers:
   * the items in order;
   * the non-vacuity notes;
   * the ledger entries;
   * the axioms used by each theorem;
   * the dependency map of Theorem 1, updated;
   * a skeleton proposal for what remains.
6. **Before you finish, check.**
   * Every file the report names is in the tarball.
   * `wc -l axioms.txt` equals the count the report gives.
   * The uploads are in `doc/batches/` and `doc/batches/skeletons/`.
   * Nothing is left at the root.
