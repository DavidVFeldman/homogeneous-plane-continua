Commission read: `doc/batches/COMMISSION-batch136.md` (batch 136 — Part D: decomposition spaces; Whyburn (6.2), (6.21); Jones 1951 Theorem 1; Jones 1955 Theorem 1).

# Report, batch 136

`lake build HPC` succeeds with `import HPC.Jones.Jones55` added at the end of `HPC.lean`. The five
new files under `HPC/Jones/` (1410 lines) contain no `sorry`. `axioms.txt` is regenerated. It has 796
lines, 46 of them new (the group "Jones 1955, decompositions (batch 136)"), and `sorryAx` occurs in
no line. The per-batch audit `doc/batches/audits/axioms-batch136.{lean,txt}` lists every theorem of
the new files, 82 entries:
* 76 show exactly `[propext, Classical.choice, Quot.sound]`;
* 4 show `[propext, Quot.sound]` (`mk_eq_mk_iff_mem_cls`, `cls_eq_of_mem`, `mk_mem_satIn`,
  `preimage_satIn`);
* 2 depend on no axioms (`mem_cls_iff`, `mem_cls_self`).

The previous `axioms.txt` is saved as `doc/batches/audits/axioms-before-batch136.txt`.

**Summary.** Every item is **proved**:
* A, decomposition spaces, including `residual_lscAt`;
* B, Jones 1941 Theorem 4 and Whyburn (6.1), (6.2), (6.21);
* C, Jones 1951 Theorem 1 (`jones51_theorem1`), closed. It is removed from `OPEN.md`;
* D, Jones 1955 Theorem 1: claims (1)–(12), the characterization of `N_o`, `N_o = L_o`, (a)–(f) of
  p. 739, and the six conclusions `jones55_b`, `jones55_c`, `jones55_usc`, `jones55_continuous`,
  `jones55_a`, `jones55_elements`.

Nothing is refuted. Nothing is left open, so `OPEN.md` gains no entry.

One new lemma does most of the work: **spreading** (`aposAt_of_isContinuum_interior`, from the
Effros theorem of batch 134). It states: in a homogeneous compact metric space, a continuum with
nonempty interior that contains `o` and misses `x` makes the space aposyndetic at `o` with respect
to `x`. With it, Theorem 1 (b) and (c) hold in every homogeneous compact metric continuum,
decomposable or not. Jones's claims (11) and (12), his case argument on p. 738 and his u.s.c.
argument are replaced (list below).

Housekeeping:
* the commission is at `doc/batches/COMMISSION-batch136.md`;
* the uploaded defects ledger ("DEFECTS-LEDGER(1).md") is at `doc/batches/DEFECTS-LEDGER.md`;
* the skeleton is at `doc/batches/skeletons/Jones55-batch136.lean`, verbatim. Its working copy
  became `HPC/Jones/Jones55.lean`, split as described below;
* the two papers are at `doc/sources/whyburn1939.pdf` and `doc/sources/jones1941.pdf`. They are
  git-ignored like the other PDFs there.

Nothing is at the root.

Edited files:
* `HPC.lean` (one import);
* `Axioms.lean` and `axioms.txt` (the new group). The batch-135 comment "Theorem 1 is open" is
  updated;
* `README.md` (the Part D entry, and the batch count 136);
* `LEDGER.md` §6 (a new subsection; the batch-135 line "Jones 1951, Theorem 1: open" now points to it);
* `OPEN.md` (the `jones51_theorem1` section is removed and a row added to *Closed items*).

No other existing file is edited. Three consequences of this rule:
* The docstrings of `HPC/Jones/Jones51.lean` (the commented-out statement at its end, `§ Jones 1951,
  Theorem 1 — not formalized`) and of `HPC/Jones/Jones48.lean` (line 27) still say that Jones 1951
  Theorem 1 is open. They are stale.
* The README's `HPC/Jones` row ("Jones 1948 and 1951") does not mention 1955.
* The README's `doc/sources/` row does not list the two new PDFs.

The batch-135 definitions (`AposAt` etc.) are **not** moved to `[TopologicalSpace X]`; the
commission's exception is not used.

## Files

| file | lines | content |
|---|---|---|
| `HPC/Jones/Decomp.lean` | 417 | item A: `AposAtT`, `IsAposyndeticT`; `cls`, `IsUSCDecomp`, `LSCAt`, `IsContinuousDecomp`; the decomposition space; `residual_lscAt` |
| `HPC/Jones/Whyburn.lean` | 99 | item B |
| `HPC/Jones/Jones55Core.lean` | 610 | item D, core: spreading; `Lset`, `CutsFrom`, `lRel`, `lSetoid`, `Nset`; (b), (c); claims (1)–(12); `N_o = L_o`; (a)–(f) |
| `HPC/Jones/Jones51Thm1.lean` | 104 | item C |
| `HPC/Jones/Jones55.lean` | 180 | umbrella; the conclusions of Jones 1955 Theorem 1 |

## Item A. Decomposition spaces — proved

* `isClosedMap_mk`, `t2Space_quotient`, `secondCountable_quotient` and `metrizableSpace_quotient`
  hold for any u.s.c. decomposition `r` of a compact metric space. Metrizability is Urysohn's
  theorem, from T2, compactness and second countability. Second countability comes from finite
  unions of basic sets, through `isOpen_satIn`.
* `isContinuum_preimage`: for a monotone decomposition, preimages of subcontinua are subcontinua.
* `exists_homeomorph_quotient`: homeomorphisms of `X` that respect `r` descend.
* `residual_lscAt`, the theorem Jones uses unstated, follows the commission's route:
  * for a countable base `B`, the sets `π(cl b)` are closed (the quotient map is closed);
  * if `r` is not l.s.c. at `x`, then `π x` is in the frontier of some `π(cl b)` with `b` near a
    point of `cls r x`;
  * frontiers of closed sets are closed and nowhere dense;
  * the intersection of their complements is residual (Baire in the compact metrizable quotient).
* `exists_lscAt` follows. Added: `lscAt_homeomorph` (continuity at an element is carried by a
  homeomorphism that respects `r`) and `isUSCDecomp_of_isClosed` (a closed equivalence relation with
  closed classes on a compact metric space is u.s.c.).
* `LSCAt` is kept in the skeleton's open-set form. There is no Hausdorff-metric restatement, so no
  equivalence is needed.

Shape changes:
* `AposAtT` (§1) has the body `IsCompact H ∧ IsConnected H` in place of `Fold.Q78.IsContinuum H`.
  The latter is declared under `[MetricSpace X]` and does not elaborate on a topological space.
  `aposAtT_iff` (`Iff.rfl`) shows it agrees with `AposAt` on metric spaces.
* `isContinuum_preimage` has the hypothesis `hK : IsCompact K ∧ IsConnected K`, for the same reason:
  `Quotient r` carries no metric instance.

## Item B. Jones 1941 Theorem 4; Whyburn (6.1), (6.2), (6.21) — proved

* `semiLocConn_of_isAposyndetic` (Jones 1941 Theorem 4, compact case) and its converse
  `isAposyndetic_of_semiLocConn` are the two directions of `theorem0` (Jones 1948, batch 135).
* `whyburn_6_1` (components of `X − x` are open) and `whyburn_6_2` (a non-separating `x` misses a
  continuum through `a` and `b`) are proved through aposyndesis, not Whyburn's components `Rᵢ` of
  `M − V_{δᵢ}(x)`. The set of points joined to `a` by a continuum missing `x` is open and closed in
  the component of `X − x` containing `a`.
* `whyburn_6_21` (cuts ⇒ separates, `CutsPts p a b → b ∉ connectedComponentIn {p}ᶜ a`) is immediate
  from (6.2).

Page-image check:
* Jones 1951 (p. 859) writes: *"In such a continuum the meaning of 'cut point' and 'separating point'
  are the same [9]"*, with [9] = Whyburn, *"Theorem 6.21"*.
* He applies it as *"Since `M′` contains a nonseparating point, every point of `M′` is a
  nonseparating point … There exists in `M′ − X` a continuum `T₁` containing `A + B`"*. That is
  "non-separating ⇒ non-cutting", the contrapositive of `whyburn_6_21`.
* Whyburn's printed (6.21) is *"Each component of `M − x` is strongly connected"*, which gives
  exactly this.

Shape change: `ha : a ≠ x` is dropped from `whyburn_6_1`. For `a = x` the component is empty.

## Item C. Jones 1951, Theorem 1 — proved

`jones51_theorem1`: a homogeneous, hereditarily unicoherent compact metric continuum is
indecomposable.

**The proof is not Jones's, and needs neither `M′` nor Whyburn.** Suppose `X` is decomposable.
1. Take `a`, and `b ∈ U_a` (claim (4)), so `L_a ≠ L_b`.
2. Let `J` be a continuum irreducible about `{a, b}`. Hereditary unicoherence of `M` puts `J` inside
   every continuum through `a` and `b` (`isContinuum_inter_of_hu`).
3. `J` is connected, so it is not the union of the disjoint closed sets `L_a ∩ J` and `L_b ∩ J`
   (by (b)). Hence some `c ∈ J` lies in a third class.
4. Then `a`, `b ∈ U_c`. By (5) some continuum through `a` and `b` misses `c`. It contains `J ∋ c`,
   a contradiction.

Shape change: `[Nontrivial X]` is dropped. A decomposable continuum is nondegenerate.

Checks asked for (page images of p. 858–859):
* **"Hereditarily unicoherent" is used three times.**
  * Twice on `M` (p. 858: *"Since `M` is hereditorily unicoherent, this is a contradiction"*;
    *"Because `M` is hereditarily unicoherent, the same reasoning holds"*).
  * Once on `M′` (p. 859: *"But `M′` is hereditarily unicoherent"*).
  * So not every use is on `M`. The use on `M′` is not shown.
* **Unicoherence of `M′` is used, not shown.** It is true (a monotone image of a hereditarily
  unicoherent continuum is hereditarily unicoherent). This is standard but not formalized here; the
  formal proof does not need it.
* *"Furthermore `M′` is homogeneous and aposyndetic"* and *"`M′` contains a nonseparating point"*
  are also asserted without argument.

## Item D. Jones 1955, Theorem 1 — proved

The definitions `Lset`, `CutsFrom`, `lRel` and `lSetoid` are verbatim from the skeleton.
`jones55_isContinuum` is `theorem3` of 1948.

**Spreading and its consequences** (`Jones55Core.lean`):
* `aposAt_of_isContinuum_interior`. Move `K` by every homeomorphism `ε`-close to the identity. Each
  image meets `K` in its interior, so the closure of the union is a continuum. It still misses `x`,
  and by Effros it contains a ball about `o`.
* `not_aposAt_trans`: if the space is not aposyndetic at `z` w.r.t. `y`, nor at `y` w.r.t. `x`,
  then not at `z` w.r.t. `x`. The continuum witnessing aposyndesis at `z` w.r.t. `x` contains a
  neighbourhood of `z`. If it missed `y` we would contradict the first hypothesis; if it contains
  `y`, spreading gives aposyndesis at `y` w.r.t. `x`.
* `aposSet_eq_of_not_aposAt`: `y ∈ L_x ⇒ U_y = U_x` (transitivity, then the Lemma of 1951).
* (b) `mem_Lset_iff_Lset_eq` and (c) `Lset_subset_of_meets`. Neither uses decomposability.

**Jones's numbered claims**, in his numbering:

| claim | Lean | proof |
|---|---|---|
| (1) | `jones55_claim1` | homogeneity (hypothesis: `M` not aposyndetic, i.e. some `L_x` nondegenerate) |
| (2) | `jones55_claim2` | p. 409 Corollary of 1948 (`totallyNonApos_exists_weakCutPoint`) + homogeneity; "cut point" = weak cut point (footnote 3) |
| (3) | `jones55_claim3` | `arcs_corollary2` moved by homogeneity (`exists_continuum_meets_of_open`); Bing's `A ⊄ R` convention is handled there |
| (4) | `jones55_claim4` | Theorem 8 of 1948 + homogeneity + `isOpen_nontrivial_of_nonempty` |
| (5) | `jones55_claim5` | Bing's Corollary 2 moved by homogeneity, as for (3) (`exists_continuum_of_mem_aposSet`) |
| (6), (7) | `jones55_claim6`, `jones55_claim7` | as printed, from (2), (5) (`cutsFrom_of_cutsPts`) and homogeneity |
| (8) | `jones55_claim8` | the Lemma of 1951 (`jones51_lemma`) |
| (9) | `jones55_claim9` | from (8) and `cutsFrom_of_cutsPts` (the tool of (5)) |
| (10) | `jones55_claim10` | as printed (closure point + the Lemma) |
| (11) | `jones55_claim11` | **replaced**: from (c) |
| (12) | `jones55_claim12` | **replaced**: from (c) and (3) (`interior_Lset_eq_empty`) |

**Then:**
* `Nset` is Jones's `N_o`.
* `Nset_characterization` gives both characterizations without `H` (footnote 4 is (b)).
* `Nset_eq_Lset` proves `N_o = M − U_o = L_o`.
* (a)–(f) of p. 739 are `jones55_prop_a` … `jones55_prop_f`.

**Conclusions** (`Jones55.lean`):
* `jones55_b`, `jones55_c`.
* `jones55_usc`, via `isClosed_lSetoid` (the relation `L_x = L_y` is closed in `X × X`, from (b)
  and the closedness of non-aposyndesis) and `isUSCDecomp_of_isClosed`.
* `jones55_continuous`, by `exists_lscAt`, `lSetoid_homeomorph` and `lscAt_homeomorph`, as printed.
* `jones55_a`: compact, connected, metrizable, nontrivial, homogeneous and aposyndetic.
* `jones55_elements`.

Shape changes:
* The skeleton's `include hX hd` is replaced by explicit hypotheses.
* `hd : IsDecomposableSpace X` is dropped from `jones55_b`, `jones55_c`, `jones55_usc`,
  `jones55_continuous` and `jones55_elements`, where it is not used. It is kept in `jones55_a`, for
  `Nontrivial (Quotient (lSetoid X))`.
* The claims are new statements, not in the skeleton. Each carries only the hypotheses it uses:
  `[Nontrivial X]` in (3), (5), (9); `hna : ¬ IsAposyndetic X` in (1), (2); `hd` in (4), (6), (7)
  and (12).

## Ledger entries (`LEDGER.md` §6, new subsection)

The outcome of each check in §3 of the commission, with the printed sentence quoted there:

1. Continuity from one element plus homogeneity: **confirmed** (`lscAt_homeomorph`).
2. (a) is not argued in the text. **Supplied**: homogeneity through `exists_homeomorph_quotient`.
   The commissioner's aposyndesis sketch is correct and is the proof of `jones55_a`.
3. "The set `N_o` is closed": **supplied but moot**, since `N_o = L_o` is closed.
4. (11) is **proved without transfinite recursion**, from (c).
5. Attainment of `d(q)` and "`E_n` is closed": **not decided, moot**. The case argument is not used.
6. "Since `M₀` is a subset of `M₁`": **the suspicion is justified**, with a sharper boundary.
   * For `o ∉ V₂`, a continuum irreducible from `o` to `cl V₂` misses `V₂` (boundary bumping), so it
     lies in `M₁`.
   * For `o ∈ V₂`, `K_o = {o} ⊄ M₁`.
   * The text does not keep `o(q)` out of `V₂`.
   * Also on p. 738: *"Since `q` does not cut `o` from `U_q` and `V₂·U_q ≠ 0`"*. The premise about
     `U_q` is drawn from `q ∉ N_o` (stated with `U_o`). That needs `U_q = U_o`, i.e. (b), which is
     not yet available there.
   * Not repaired in place, because the argument is replaced as a whole.
7. `R_r(p)·R_s(p)` with `s = 1/n′ − r`: **the reading is right** (triangle inequality).
8. (4): **confirmed** (`jones55_claim4`).
9. Degenerate case: **confirmed**. `G` is then the decomposition into points, and "nondegenerate"
   refers to `G` as a space. The formal statements need no case split.
10. The semi-metric/Moore-space remark is **not used**.

Also recorded:
* Jones 1951's unproved uses on `M′` (hereditary unicoherence, homogeneity, aposyndesis, a
  nonseparating point);
* Whyburn's and Jones 1941's printed statements.

## Jones 1955 Theorem 1: sentences replaced

| printed sentence (place) | replaced by |
|---|---|
| (11): *"Suppose that for each point `o` of `H`, `o` does not cut all other points of `N_o` from `U` … Thus one obtains an uncountable well-ordered monotone decreasing sequence of distinct closed subsets of a compact metric space. This being impossible …"* (p. 737) | `jones55_claim11`, from (c) |
| (12): *"It follows from (3) and (11) that `N_o` contains no (rel.) open subset of `M`. … By Theorem 6 of [11] `D` contains a point `w` … which is a contradiction."* (p. 737) | `jones55_claim12`, from (c) and (3); Theorem 6 of 1948 is not used |
| *"The set `N_o` is closed."* (p. 737) | `Nset_eq_Lset` + `isClosed_Lset` |
| The case argument, from *"Now suppose that for some point `o` of `M`, `N_o + U_o ≠ M`"* to *"Hence `x` does not cut `y` from `U_o`, which is a contradiction"* (pp. 737–738), and *"It follows from the preceding paragraph that for each point `o` of `M`, `N_o = M − U_o`"* | `Nset_eq_Lset`, from (b) and (c), through spreading |
| *"Furthermore `G` is upper semi-continuous. For if this were not the case `G` would contain a convergence sequence of elements … This is a contradiction of (f)."* (p. 739) | `isClosed_lSetoid` + `isUSCDecomp_of_isClosed` |
| (a): not argued (p. 739) | `jones55_a` (homogeneity: `exists_homeomorph_quotient`; aposyndesis: the commissioner's sketch) |

Kept as printed:
* the first paragraph (degenerate case);
* (1)–(10);
* the characterization of `N_o` (Jones derives the first form from (4) and (12), the second from
  (11); so is it here);
* (a)–(f);
* the last sentence (continuity).

## What Theorem 2 needs beyond Moore's theorem

Theorem 2 (p. 739): if `M` is a homogeneous, decomposable, bounded plane continuum, then `G = {L_x}`
is continuous, `G` is a simple closed curve, and each element is a homogeneous plane continuum that
does not separate the plane. Its proof, step by step:

1. *"It is clear that for each `g` of `G`, `M − g` is connected (in fact, by (5), `M − g` is strongly
   or continuum-wise connected)."* Available: (c) and (5) give it (`jones55_claim5`, `jones55_prop_e`).
2. *"Since each two elements of `G` are homeomorphic, it follows that if one element of `G` were to
   separate `S`, then each of them would separate `S`."* This needs **Borsuk's theorem**: whether a
   plane compactum separates the plane is a topological invariant (e.g. through Čech `H¹` or
   Janiszewski-type duality). It is not in the repository and not in Mathlib. `jones55_elements`
   supplies the homeomorphisms.
3. *"… and there would exist uncountably many mutually exclusive domains (at least one for each `g`)
   in the plane. This being impossible …"* This needs an argument the text does not give.
   * Choose, for each `g`, a complementary domain `W_g` of `g` not containing the connected set
     `M − g`. Then `W_g ∩ M = ∅`.
   * For `g ≠ g′`, `W_g ∩ W_{g′} ≠ ∅` forces `W_g ⊆ W_{g′}` and then `∂W_g ⊆ ∂W_{g′}`. That is
     impossible, since `∂W_g ⊆ g`, `∂W_{g′} ⊆ g′`, and `g ∩ g′ = ∅`.
   * `G` is uncountable, being a nondegenerate continuum (`jones55_a`).
   * The plane is second countable, so it has no uncountable disjoint family of open sets.
   * All of this is elementary, but needs to be written.
4. *"Let `G′` denote the upper semi-continuous collection consisting of `G` together with each
   degenerate subset of `S − M`."* The **upper semicontinuity of `G′` is asserted**. It follows from
   `jones55_usc` and the closedness of `M`; easy, but unproved in the text.
5. *"With respect to its elements (as points), `G′` is a plane [13]"*: **Moore's theorem** (1925),
   the Moore decision of notes §168. Its hypotheses are an u.s.c. decomposition of the plane into
   non-separating continua (step 2 for the elements of `G`).
6. *"… and `G` is a compact subcontinuum of `G′`."* The decomposition space `M/G` embeds in `S/G′`:
   `M` is closed and saturated, and the two quotient topologies agree on it. Easy, with item A.
7. *"Furthermore, `G` is homogeneous and aposyndetic. Hence by [5], `G` is a simple closed curve."*
   Homogeneity and aposyndesis are `jones55_a`. The cited result is Jones 1949, *A note on
   homogeneous plane continua* (a homogeneous aposyndetic bounded plane continuum is a simple closed
   curve), which is [3] in the paper; [5] is Jones 1951. This citation slip was already recorded in
   batch 135. **Jones 1949 is needed** and is not in `doc/sources/`.

So, beyond Moore's theorem, Theorem 2 needs:
* Borsuk's invariance of plane separation;
* the uncountably-many-domains argument;
* the u.s.c. of `G′`;
* the embedding of `M/G` in `S/G′`;
* Jones 1949.

Part (2) of Theorem 2 ("does not separate the plane") is step 2–3. The homogeneity of the elements
is `jones55_elements`.
